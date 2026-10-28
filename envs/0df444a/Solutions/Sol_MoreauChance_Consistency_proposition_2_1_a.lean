-- Prove2me | solution 1 for MoreauChance.Consistency.proposition_2_1_a
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:06:43.865118+00:00
-- url     : https://prove2.me/submissions/8e74d22f-4a6f-437d-b800-183220145614

import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting
import Init
import Mathlib



section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency
universe u
variable {E : Type u} [NormedAddCommGroup E]

theorem envelope_le (f : E → EReal) (lam : ℝ) (x : E) : moreauEnv f lam x ≤ f x := by
  calc
    _ ≤ f x + ((‖x-x‖^2 / (2*lam) : ℝ) : EReal) := iInf_le _ x
    _ = f x := by simp

theorem envelope_antitone_parameter (f : E → EReal) (l1 l2 : ℝ) (hl2 : 0 < l2)
    (hle : l2 ≤ l1) (x : E) : moreauEnv f l1 x ≤ moreauEnv f l2 x := by
  apply iInf_mono
  intro z
  apply add_le_add (le_refl (f z))
  exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))

theorem envelope_mono_function (f g : E → EReal) (hfg : ∀ z, f z ≤ g z) (lam : ℝ) (x : E) :
    moreauEnv f lam x ≤ moreauEnv g lam x := by
  exact iInf_mono (fun z => add_le_add (hfg z) (le_refl _))

theorem envelope_constant (c : ℝ) (lam : ℝ) (hlam : 0 < lam) (x : E) :
    moreauEnv (fun _ : E => (c : EReal)) lam x = c := by
  apply le_antisymm (envelope_le _ _ _)
  apply le_iInf
  intro z
  have hp : (0 : EReal) ≤ ((‖x-z‖^2/(2*lam) : ℝ) : EReal) := by
    exact_mod_cast div_nonneg (sq_nonneg _) (by positivity : 0 ≤ 2*lam)
  simpa using add_le_add (le_refl (c : EReal)) hp

end Queelius.MoreauChance

end

section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency MeasureTheory
universe u
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def coneOf (K : Set Y) (hne : K.Nonempty) (hc : Convex ℝ K)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) (hclosed : IsClosed K) : ProperCone ℝ Y where
  carrier := K
  zero_mem' := by
    obtain ⟨y,hy⟩ := hne
    simpa using hs 0 (le_refl 0) y hy
  add_mem' := by
    intro x y hx hy
    have hh := hc hx hy (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
    have h := hs 2 (by norm_num) _ hh
    convert h using 1 <;> module
  smul_mem' := by
    intro t y hy
    exact hs t.val t.property y hy
  isClosed' := hclosed

theorem closed_cone_polar_iff (K : Set Y) (hne : K.Nonempty) (hc : Convex ℝ K)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) (hclosed : IsClosed K) (y : Y) :
    y ∈ K ↔ ∀ v : StrongDual ℝ Y, (∀ z ∈ K, 0 ≤ v z) → 0 ≤ v y := by
  constructor
  · intro hy v hv; exact hv y hy
  · intro h
    by_contra hy
    obtain ⟨v,hv,hvy⟩ := (coneOf K hne hc hs hclosed).hyperplane_separation_point hy
    exact (not_lt_of_ge (h v hv)) hvy

theorem generator_subset_polar (K : Set Y) (C : Set (StrongDual ℝ Y))
    (hgen : closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) =
      StrongDual.toWeakDual '' {v | ∀ y ∈ K, 0 ≤ v y}) :
    ∀ v ∈ C, ∀ y ∈ K, 0 ≤ v y := by
  intro v hv
  have hm : StrongDual.toWeakDual v ∈ closure
      (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) := by
    apply subset_closure
    exact ⟨v,⟨1,by norm_num,v,hv,by simp⟩,rfl⟩
  rw [hgen] at hm
  rcases hm with ⟨v',hv',heq⟩
  have hveq : v'=v := StrongDual.toWeakDual.injective heq
  simpa [hveq] using hv'

theorem generator_test_iff (K : Set Y) (C : Set (StrongDual ℝ Y))
    (hgen : closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) =
      StrongDual.toWeakDual '' {v | ∀ y ∈ K, 0 ≤ v y}) (y : Y) :
    (∀ v ∈ C, v y ≤ 0) ↔ (∀ v : StrongDual ℝ Y, (∀ z ∈ K, 0 ≤ v z) → v y ≤ 0) := by
  constructor
  · intro h v hv
    have hclosed : IsClosed {w : WeakDual ℝ Y | w y ≤ 0} :=
      isClosed_le (WeakDual.eval_continuous y) continuous_const
    have hsub : closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) ⊆
        {w : WeakDual ℝ Y | w y ≤ 0} := by
      apply hclosed.closure_subset_iff.mpr
      rintro w ⟨v,⟨t,ht,v',hv',rfl⟩,rfl⟩
      change t * v' y ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos ht (h v' hv')
    apply hsub
    rw [hgen]
    exact ⟨v,hv,rfl⟩
  · intro h v hv
    exact h v (generator_subset_polar K C hgen v hv)

theorem negative_cone_scalarization (K : Set Y) (C : Set (StrongDual ℝ Y))
    (hne : K.Nonempty) (hc : Convex ℝ K)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) (hclosed : IsClosed K)
    (hgen : closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) =
      StrongDual.toWeakDual '' {v | ∀ y ∈ K, 0 ≤ v y}) (y : Y) :
    -y ∈ K ↔ ∀ v ∈ C, v y ≤ 0 := by
  rw [generator_test_iff K C hgen y,closed_cone_polar_iff K hne hc hs hclosed]
  simp only [map_neg,neg_nonneg]

end Queelius.MoreauChance

end

section
noncomputable section
open MeasureTheory Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem supFun_le_iff {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (x : H) (z : EuclideanSpace ℝ (Fin m)) :
    supFun C h Φ (WithLp.toLp 2 (x,z)) ≤ (h x : EReal) ↔ ∀ v ∈ C, v (Φ x z) ≤ 0 := by
  simp only [supFun,WithLp.ofLp_toLp,iSup_le_iff,EReal.coe_le_coe_iff]
  constructor
  · intro hh v hv; have := hh v hv; linarith
  · intro hh v hv; have := hh v hv; linarith

theorem conic_event_equivalence {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ) (x : H) (z : EuclideanSpace ℝ (Fin m)) :
    -(Φ x z) ∈ K ↔ supFun C h Φ (WithLp.toLp 2 (x,z)) ≤ (h x : EReal) := by
  rw [supFun_le_iff]
  exact negative_cone_scalarization K C hset.K_nonempty hset.K_convex hset.K_cone
    hset.K_closed hset.C_generates_polar (Φ x z)

theorem generator_nonempty {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : Set Y) (C : Set (StrongDual ℝ Y))
    (hgen : closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) =
      StrongDual.toWeakDual '' {v | ∀ y ∈ K, 0 ≤ v y}) : C.Nonempty := by
  by_contra hC
  have he : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
  have hz : StrongDual.toWeakDual (0 : StrongDual ℝ Y) ∈ closure
      (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w=t • v}) := by
    rw [hgen]
    exact ⟨0,by simp,rfl⟩
  simpa [he] using hz

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem proposition_2_6
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ) :
    ∀ x : H, probFun K Φ μ ξ x =
      μ {ω | supFun C h Φ (WithLp.toLp 2 (x, ξ ω)) ≤ (h x : EReal)} := by
  intro x
  unfold probFun
  congr 1
  ext ω
  exact Queelius.MoreauChance.conic_event_equivalence K C h Φ hset x (ξ ω)

end MoreauChance.Consistency

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_lower_envelope (g : E → ℝ) (L : E →L[ℝ] ℝ) (c : ℝ)
    (hminor : ∀ z, L z+c ≤ g z) (lam : ℝ) (hlam : 0 < lam) (x : E) :
    ((L x+c-lam*‖L‖^2/2 : ℝ) : EReal) ≤ moreauEnv (fun z => (g z : EReal)) lam x := by
  apply le_iInf
  intro z
  rw [← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  have hL : L x - L z ≤ ‖L‖ * ‖x-z‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans (L.le_opNorm (x-z))
  have hyoung : ‖L‖ * ‖x-z‖ - lam*‖L‖^2/2 ≤ ‖x-z‖^2/(2*lam) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*lam)).mpr
    nlinarith [sq_nonneg (‖x-z‖-lam*‖L‖)]
  have hg := hminor z
  linarith

theorem envelope_tendsto (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_lsc : LowerSemicontinuous g) (x : E) :
    Tendsto (fun l => moreauEnv (fun z => (g z : EReal)) l x) (𝓝[>] 0) (𝓝 (g x : EReal)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,har,hr⟩ := EReal.exists_rat_btwn_of_lt ha
    have hrg : (r : ℝ) < g x := EReal.coe_lt_coe_iff.mp hr
    obtain ⟨L,c,hminor,htouch⟩ := ConvexOn.exists_affine_le_of_lt (𝕜:=ℝ)
      (s:=Set.univ) (φ:=g) (x:=x) (a:=(r:ℝ)) (Set.mem_univ x) hrg
      isClosed_univ (hg_lsc.lowerSemicontinuousOn Set.univ) hg_convex
    have hminor' (z : E) : L z+c ≤ g z := by simpa using hminor ⟨z,Set.mem_univ z⟩
    have htouch' : L x+c = (r : ℝ) := by simpa using htouch
    have hcont : Continuous (fun l : ℝ => ((L x+c-l*‖L‖^2/2 : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    have hlim : Tendsto (fun l : ℝ => ((L x+c-l*‖L‖^2/2 : ℝ) : EReal))
        (𝓝[>] 0) (𝓝 ((r : ℝ) : EReal)) := by
      simpa [htouch'] using (hcont.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
    filter_upwards [hlim.eventually (eventually_gt_nhds har),self_mem_nhdsWithin] with l hl hlpos
    exact hl.trans_le (affine_lower_envelope g L c hminor' l hlpos x)
  · intro b hb
    exact Filter.Eventually.of_forall (fun l => (envelope_le (fun z => (g z : EReal)) l x).trans_lt hb)

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem proposition_2_1_a
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (g : H → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g) (x : H) :
    (∀ l1 l2 : ℝ, 0 < l2 → l2 < l1 →
        moreauEnv (fun z => (g z : EReal)) l1 x ≤ moreauEnv (fun z => (g z : EReal)) l2 x) ∧
      (∀ l : ℝ, 0 < l → moreauEnv (fun z => (g z : EReal)) l x ≤ (g x : EReal)) ∧
      Tendsto (fun l => moreauEnv (fun z => (g z : EReal)) l x) (𝓝[>] 0) (𝓝 (g x : EReal)) := by
  exact ⟨fun l1 l2 hl2 hle => Queelius.MoreauChance.envelope_antitone_parameter _ l1 l2 hl2 hle.le x,
    (fun l hl => Queelius.MoreauChance.envelope_le _ l x),
    Queelius.MoreauChance.envelope_tendsto g hg_convex hg_lsc x⟩

end MoreauChance.Consistency

end

section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency MeasureTheory
variable {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}

theorem probability_parameter_mono (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m))
    (l1 l2 : ℝ) (hl2 : 0 < l2) (hle : l2 ≤ l1) (x : H) :
    probFunReg C h Φ μ ξ l2 x ≤ probFunReg C h Φ μ ξ l1 x := by
  apply measure_mono
  intro ω hω
  exact (envelope_antitone_parameter (supFun C h Φ) l1 l2 hl2 hle _).trans hω

theorem probability_le_regularized (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (lam : ℝ) (x : H) :
    probFun K Φ μ ξ x ≤ probFunReg C h Φ μ ξ lam x := by
  apply measure_mono
  intro ω hω
  exact (envelope_le (supFun C h Φ) lam _).trans ((conic_event_equivalence K C h Φ hset x (ξ ω)).mp hω)

theorem feasible_inclusion (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (lam p : ℝ) :
    feasSet K Φ μ ξ p ⊆ feasSetReg C h Φ μ ξ lam p := by
  intro x hx
  exact hx.trans (probability_le_regularized K C h Φ hset μ ξ lam x)

theorem value_upper_bound (ψ : H → EReal) (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (lam p : ℝ) :
    valPReg ψ C h Φ μ ξ lam p ≤ valP ψ K Φ μ ξ p := by
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  exact (iInf_le_of_le x (iInf_le _ (feasible_inclusion K C h Φ hset μ ξ lam p hx))).trans
    (envelope_le ψ lam x)

end Queelius.MoreauChance

end

section
open MeasureTheory MoreauChance.Consistency

theorem submission_primary_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ) :
    ∀ x : H, probFun K Φ μ ξ x =
      μ {ω | supFun C h Φ (WithLp.toLp 2 (x, ξ ω)) ≤ (h x : EReal)} :=
  proposition_2_6 μ ξ hξ K C h Φ hset

end

section
noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem weakConv_dual_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (xk : ℕ → H) (x : H) (hx : WeakConv xk x) (L : H →L[ℝ] ℝ) :
    Tendsto (fun k => L (xk k)) atTop (𝓝 (L x)) := by
  let v := (InnerProductSpace.toDual ℝ H).symm L
  have heq (y : H) : ⟪y,v⟫_ℝ = L y := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [heq] using hx v

theorem envelope_weak_liminf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_lsc : LowerSemicontinuous g) (xk : ℕ → H) (x : H) (lamk : ℕ → ℝ)
    (hxk : WeakConv xk x) (hlam_pos : ∀ k, 0 < lamk k) (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    (g x : EReal) ≤ Filter.liminf (fun k => moreauEnv (fun z => (g z : EReal)) (lamk k) (xk k)) atTop := by
  rw [le_liminf_iff]
  intro a ha
  obtain ⟨r,har,hr⟩ := EReal.exists_rat_btwn_of_lt ha
  obtain ⟨L,c,hminor,htouch⟩ := ConvexOn.exists_affine_le_of_lt (𝕜:=ℝ)
    (s:=Set.univ) (φ:=g) (x:=x) (a:=(r:ℝ)) (Set.mem_univ x) (EReal.coe_lt_coe_iff.mp hr)
    isClosed_univ (hg_lsc.lowerSemicontinuousOn Set.univ) hg_convex
  have hminor' (z : H) : L z+c ≤ g z := by simpa using hminor ⟨z,Set.mem_univ z⟩
  have htouch' : L x+c = (r : ℝ) := by simpa using htouch
  have hreal : Tendsto (fun k => L (xk k)+c-lamk k*‖L‖^2/2) atTop (𝓝 (r : ℝ)) := by
    simpa [htouch'] using ((weakConv_dual_tendsto xk x hxk L).add_const c).sub
      ((hlam_lim.mul_const (‖L‖^2)).div_const 2)
  have hlim := (continuous_coe_real_ereal.tendsto (r : ℝ)).comp hreal
  filter_upwards [hlim.eventually (eventually_gt_nhds har)] with k hk
  exact hk.trans_le (affine_lower_envelope g L c hminor' (lamk k) (hlam_pos k) (xk k))

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem proposition_2_1_c
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (g : H → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g)
    (xk : ℕ → H) (x : H) (lamk : ℕ → ℝ) (hxk : WeakConv xk x) (hlam_pos : ∀ k, 0 < lamk k)
    (hlam_anti : Antitone lamk) (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    (g x : EReal) ≤
      Filter.liminf (fun k => moreauEnv (fun z => (g z : EReal)) (lamk k) (xk k)) atTop :=
  Queelius.MoreauChance.envelope_weak_liminf g hg_convex hg_lsc xk x lamk hxk hlam_pos hlam_lim

end MoreauChance.Consistency

end

section
noncomputable section
namespace Queelius.MoreauChance.Controls
open MoreauChance.Consistency

theorem quadratic_complete_square (lam x z : ℝ) (hlam : 0 < lam) :
    z^2+(x-z)^2/(2*lam) = x^2/(1+2*lam) + (1+2*lam)/(2*lam)*(z-x/(1+2*lam))^2 := by
  have h0 : lam ≠ 0 := ne_of_gt hlam
  have hd : 1+2*lam ≠ 0 := by linarith
  field_simp
  ring

theorem quadratic_envelope (lam x : ℝ) (hlam : 0 < lam) :
    moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) lam x = ((x^2/(1+2*lam) : ℝ) : EReal) := by
  apply le_antisymm
  · calc
      _ ≤ (((x/(1+2*lam))^2 : ℝ) : EReal) + ((‖x-x/(1+2*lam)‖^2/(2*lam) : ℝ) : EReal) :=
        iInf_le _ (x/(1+2*lam))
      _ = _ := by
        rw [← EReal.coe_add,Real.norm_eq_abs,sq_abs,quadratic_complete_square lam x _ hlam]
        simp
  · apply le_iInf
    intro z
    rw [← EReal.coe_add,Real.norm_eq_abs,sq_abs,quadratic_complete_square lam x z hlam]
    apply EReal.coe_le_coe_iff.mpr
    have hn : 0 ≤ (1+2*lam)/(2*lam)*(z-x/(1+2*lam))^2 := by positivity
    linarith

theorem quadratic_at_one : moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) 1 3 = ((3 : ℝ) : EReal) := by
  rw [quadratic_envelope 1 3 (by norm_num)]
  norm_num

theorem quadratic_strict_parameter :
    moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) 2 3 <
      moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) 1 3 := by
  rw [quadratic_envelope 2 3 (by norm_num),quadratic_at_one]
  norm_num

theorem scalar_halfline_event (x : ℝ) (z : EuclideanSpace ℝ (Fin 0)) :
    supFun {(ContinuousLinearMap.id ℝ ℝ)} (fun _ : ℝ => 0)
      (fun (x : ℝ) (_ : EuclideanSpace ℝ (Fin 0)) => x) (WithLp.toLp 2 (x,z)) ≤ 0 ↔ x ≤ 0 := by
  simp [supFun]

theorem empty_generator_is_not_a_conic_model :
    supFun (∅ : Set (StrongDual ℝ ℝ)) (fun _ : ℝ => 0)
      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 0)) => (1 : ℝ)) (WithLp.toLp 2 (0,0)) ≤ 0 ∧
    - (1 : ℝ) ∉ ({0} : Set ℝ) := by
  constructor
  · simp [supFun]
  · norm_num

end Queelius.MoreauChance.Controls

end

section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency Filter Topology

variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}

theorem supFun_attained (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hne : C.Nonempty)
    (hc : IsCompact (StrongDual.toWeakDual '' C))
    (q : WithLp 2 (H × EuclideanSpace ℝ (Fin m))) :
    ∃ v ∈ C, supFun C h Φ q =
      ((v (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) + h (WithLp.ofLp q).1 : ℝ) : EReal) := by
  obtain ⟨w,hw,hmax⟩ := hc.exists_isMaxOn (hne.image _)
    (WeakDual.eval_continuous (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2)).continuousOn
  rcases hw with ⟨v,hv,rfl⟩
  refine ⟨v,hv,le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply EReal.coe_le_coe_iff.mpr
    have hh := hmax (show StrongDual.toWeakDual u ∈ StrongDual.toWeakDual '' C from ⟨u,hu,rfl⟩)
    change u (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) ≤ v (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) at hh
    linarith
  · exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

def realSupFun (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (q : WithLp 2 (H × EuclideanSpace ℝ (Fin m))) : ℝ := (supFun C h Φ q).toReal

theorem coe_realSupFun (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hne : C.Nonempty)
    (hc : IsCompact (StrongDual.toWeakDual '' C))
    (q : WithLp 2 (H × EuclideanSpace ℝ (Fin m))) :
    (realSupFun C h Φ q : EReal) = supFun C h Φ q := by
  obtain ⟨v,hv,he⟩ := supFun_attained C h Φ hne hc q
  unfold realSupFun
  rw [he,EReal.toReal_coe]

theorem realSupFun_le_iff (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hne : C.Nonempty)
    (hc : IsCompact (StrongDual.toWeakDual '' C))
    (q : WithLp 2 (H × EuclideanSpace ℝ (Fin m))) (r : ℝ) :
    realSupFun C h Φ q ≤ r ↔ ∀ v ∈ C,
      v (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) + h (WithLp.ofLp q).1 ≤ r := by
  rw [← EReal.coe_le_coe_iff,coe_realSupFun C h Φ hne hc]
  simp only [supFun,iSup_le_iff,EReal.coe_le_coe_iff]

theorem realSupFun_convex (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ) :
    ConvexOn ℝ Set.univ (realSupFun C h Φ) := by
  have hn := generator_nonempty K C hset.C_generates_polar
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  apply (realSupFun_le_iff C h Φ hn hset.C_weakStarCompact _ _).mpr
  intro v hv
  have hh := (hset.scalarization_convex v hv).2 (Set.mem_univ (WithLp.ofLp x))
    (Set.mem_univ (WithLp.ofLp y)) ha hb hab
  have hxv := (realSupFun_le_iff C h Φ hn hset.C_weakStarCompact x _).mp le_rfl v hv
  have hyv := (realSupFun_le_iff C h Φ hn hset.C_weakStarCompact y _).mp le_rfl v hv
  change v (Φ (a • WithLp.ofLp x + b • WithLp.ofLp y).1
    (a • WithLp.ofLp x + b • WithLp.ofLp y).2) + h (a • WithLp.ofLp x + b • WithLp.ofLp y).1 ≤ _
  exact hh.trans (add_le_add (smul_le_smul_of_nonneg_left hxv ha) (smul_le_smul_of_nonneg_left hyv hb))

theorem realSupFun_lsc (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2)) :
    LowerSemicontinuous (realSupFun C h Φ) := by
  have hn := generator_nonempty K C hset.C_generates_polar
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  have he : {q | realSupFun C h Φ q ≤ r} =
      ⋂ v ∈ C, {q : WithLp 2 (H × EuclideanSpace ℝ (Fin m)) |
        v (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) + h (WithLp.ofLp q).1 ≤ r} := by
    ext q
    simp only [Set.mem_setOf_eq,Set.mem_iInter,realSupFun_le_iff C h Φ hn hset.C_weakStarCompact]
  change IsClosed {q | realSupFun C h Φ q ≤ r}
  rw [he]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  apply isClosed_le _ continuous_const
  have hh := hset.h_C1.continuous
  fun_prop

end Queelius.MoreauChance

end

section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency MeasureTheory Filter Topology

theorem envelope_usc {E : Type*} [NormedAddCommGroup E] (g : E → ℝ) (lam : ℝ) :
    UpperSemicontinuous (moreauEnv (fun z => (g z : EReal)) lam) := by
  apply upperSemicontinuous_iInf
  intro z
  have hc : Continuous (fun x : E => ((g z + ‖x-z‖^2/(2*lam) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  simpa only [EReal.coe_add] using hc.upperSemicontinuous

theorem envelope_event_measurable {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (g : E → ℝ) (lam : ℝ) (X : Ω → E) (hX : Measurable X) (r : ℝ) :
    MeasurableSet {ω | moreauEnv (fun z => (g z : EReal)) lam (X ω) ≤ (r : EReal)} :=
  measurableSet_le ((envelope_usc g lam).measurable.comp hX) measurable_const

theorem envelope_event_intersection {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (hgl : LowerSemicontinuous g)
    (X : Ω → E) (r : ℝ) :
    (⋂ lam : {l : ℝ // 0 < l}, {ω | moreauEnv (fun z => (g z : EReal)) lam (X ω) ≤ (r : EReal)}) =
      {ω | g (X ω) ≤ r} := by
  ext ω
  simp only [Set.mem_iInter,Set.mem_setOf_eq]
  constructor
  · intro h
    have he : ∀ᶠ l in 𝓝[>] (0 : ℝ), moreauEnv (fun z => (g z : EReal)) l (X ω) ≤ (r : EReal) := by
      filter_upwards [self_mem_nhdsWithin] with l hl
      exact h ⟨l,hl⟩
    exact EReal.coe_le_coe_iff.mp (le_of_tendsto (envelope_tendsto g hg hgl (X ω)) he)
  · intro h l
    exact (envelope_le (fun z => (g z : EReal)) l (X ω)).trans (EReal.coe_le_coe_iff.mpr h)

theorem envelope_probability_inf {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (hgl : LowerSemicontinuous g)
    (X : Ω → E) (hX : Measurable X) (r : ℝ) :
    (⨅ (l : ℝ) (_ : 0 < l), μ {ω | moreauEnv (fun z => (g z : EReal)) l (X ω) ≤ (r : EReal)}) =
      μ {ω | g (X ω) ≤ r} := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hp (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have ha : Antitone lam := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hab 1
  have hl : Tendsto lam atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall hp⟩
  let A : ℕ → Set Ω := fun n =>
    {ω | moreauEnv (fun z => (g z : EReal)) (lam n) (X ω) ≤ (r : EReal)}
  have hm : Antitone A := by
    intro a b hab ω hω
    exact (envelope_antitone_parameter _ (lam a) (lam b) (hp b) (ha hab) (X ω)).trans hω
  have hi : (⋂ n, A n) = {ω | g (X ω) ≤ r} := by
    ext ω
    simp only [Set.mem_iInter,Set.mem_setOf_eq,A]
    constructor
    · intro h
      exact EReal.coe_le_coe_iff.mp (le_of_tendsto
        ((envelope_tendsto g hg hgl (X ω)).comp hl) (Filter.Eventually.of_forall h))
    · intro h n
      exact (envelope_le (fun z => (g z : EReal)) (lam n) (X ω)).trans
        (EReal.coe_le_coe_iff.mpr h)
  have he := hm.measure_iInter (fun n => (envelope_event_measurable g (lam n) X hX r).nullMeasurableSet)
    ⟨0,measure_ne_top μ _⟩
  rw [hi] at he
  apply le_antisymm
  · rw [he]
    apply le_iInf
    intro n
    exact iInf_le_of_le (lam n) (iInf_le _ (hp n))
  · apply le_iInf
    intro l
    apply le_iInf
    intro hl
    apply measure_mono
    intro ω hω
    exact (envelope_le (fun z => (g z : EReal)) l (X ω)).trans
      (EReal.coe_le_coe_iff.mpr hω)

end Queelius.MoreauChance

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem ereal_real_epigraph_closed (f : H → EReal) (hf : LowerSemicontinuous f) :
    IsClosed {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
  exact hf.isClosed_epigraph.preimage
    (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

theorem dual_product_coordinates (L : (H × ℝ) →L[ℝ] ℝ) (x : H) (t : ℝ) :
    L (x,t) = L (x,0) + L (0,1) * t := by
  have h1 : (x,t) = (x,0) + t • (0,1) := by ext <;> simp
  rw [h1,map_add,map_smul]
  simp [mul_comm]

theorem epigraph_separator_vertical_nonneg (f : H → EReal)
    (hf : ∃ x : H, ∃ a : ℝ, f x = (a : EReal))
    (L : (H × ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hb : ∀ q : H × ℝ, f q.1 ≤ (q.2 : EReal) → b < L q) : 0 ≤ L (0,1) := by
  obtain ⟨x,a,ha⟩ := hf
  have h0 := hb (x,a) (by simp [ha])
  rw [dual_product_coordinates] at h0
  by_contra hn
  have hv : L (0,1) < 0 := lt_of_not_ge hn
  let t := (L (x,0) + L (0,1)*a-b+1)/(-L (0,1))
  have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hv)
  have hh := hb (x,a+t) (by simp only [ha,EReal.coe_le_coe_iff]; linarith)
  rw [dual_product_coordinates] at hh
  have hcancel : t * (-L (0,1)) = L (x,0) + L (0,1)*a-b+1 :=
    div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hv))
  nlinarith

theorem positive_separator_affine (f : H → EReal) (hnobot : ∀ x, f x ≠ ⊥)
    (L : (H × ℝ) →L[ℝ] ℝ) (b : ℝ) (hv : 0 < L (0,1))
    (hb : ∀ q : H × ℝ, f q.1 ≤ (q.2 : EReal) → b < L q) :
    ∃ (l : H →L[ℝ] ℝ) (c : ℝ),
      (∀ z, ((l z+c : ℝ) : EReal) ≤ f z) ∧
      ∀ x a, L (x,a) < b → a < l x+c := by
  let v := L (0,1)
  let l : H →L[ℝ] ℝ := -(v⁻¹) • L.comp (ContinuousLinearMap.inl ℝ H ℝ)
  let c := b/v
  refine ⟨l,c,?_,?_⟩
  · intro z
    by_cases hz : f z = ⊤
    · simp [hz]
    · have he := EReal.coe_toReal hz (hnobot z)
      rw [← he,EReal.coe_le_coe_iff]
      have h := hb (z,(f z).toReal) (by simp [he])
      rw [dual_product_coordinates] at h
      have hv' : 0 < v := hv
      change -(v⁻¹) * L (z,0) + b/v ≤ (f z).toReal
      have hh : (b-L (z,0))/v ≤ (f z).toReal :=
        (div_le_iff₀ hv').mpr (by nlinarith)
      convert hh using 1 <;> ring
  · intro x a ha
    rw [dual_product_coordinates] at ha
    change a < -(v⁻¹) * L (x,0) + b/v
    have hv' : 0 < v := hv
    have h : a < (b-L (x,0))/v := (lt_div_iff₀ hv').mpr (by nlinarith)
    convert h using 1 <;> ring

theorem gamma_has_affine_minorant (f : H → EReal) (hf : IsGammaZero f) :
    ∃ (l : H →L[ℝ] ℝ) (c : ℝ), ∀ z, ((l z+c : ℝ) : EReal) ≤ f z := by
  obtain ⟨x,hx⟩ := hf.2.1
  have he := EReal.coe_toReal hx (hf.1 x)
  let a := (f x).toReal-1
  have hbelow : (a : EReal) < f x := by rw [← he,EReal.coe_lt_coe_iff]; dsimp [a]; linarith
  obtain ⟨L,b,hl,hb⟩ := geometric_hahn_banach_point_closed (x := (x,a)) hf.2.2.1
    (ereal_real_epigraph_closed f hf.2.2.2) (not_le_of_gt hbelow)
  have hfinite := hb (x,(f x).toReal) (by simp [he])
  have hv : 0 < L (0,1) := by
    rw [dual_product_coordinates] at hl hfinite
    dsimp [a] at hl
    nlinarith
  obtain ⟨l,c,hminor,_⟩ := positive_separator_affine f hf.1 L b hv hb
  exact ⟨l,c,hminor⟩

theorem gamma_affine_support_below (f : H → EReal) (hf : IsGammaZero f)
    (x : H) (r : ℝ) (hr : (r : EReal) < f x) :
    ∃ (l : H →L[ℝ] ℝ) (c : ℝ),
      (∀ z, ((l z+c : ℝ) : EReal) ≤ f z) ∧ r < l x+c := by
  obtain ⟨l,c,hminor⟩ := gamma_has_affine_minorant f hf
  obtain ⟨L,b,hl,hb⟩ := geometric_hahn_banach_point_closed (x := (x,r)) hf.2.2.1
    (ereal_real_epigraph_closed f hf.2.2.2) (not_le_of_gt hr)
  obtain ⟨y,hy⟩ := hf.2.1
  have hv : 0 ≤ L (0,1) := epigraph_separator_vertical_nonneg f
    ⟨y,(f y).toReal,(EReal.coe_toReal hy (hf.1 y)).symm⟩ L b hb
  let A : (H × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ H ℝ -
    l.comp (ContinuousLinearMap.fst ℝ H ℝ)
  have hA (q : H × ℝ) (hq : f q.1 ≤ (q.2 : EReal)) : c ≤ A q := by
    have h := EReal.coe_le_coe_iff.mp ((hminor q.1).trans hq)
    change c ≤ q.2-l q.1
    linarith
  have hc : Continuous (fun ε : ℝ => (L+ε • A) (x,r) - (b+ε*c)) := by fun_prop
  have hevent : ∀ᶠ ε in 𝓝 (0 : ℝ), (L+ε • A) (x,r) - (b+ε*c) < 0 := by
    apply hc.continuousAt.eventually_lt continuousAt_const
    simpa using sub_neg.mpr hl
  have hpositive : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hsep⟩ := (Filter.Eventually.and hpositive
    (hevent.filter_mono nhdsWithin_le_nhds)).exists
  have hpos : 0 < (L+ε • A) (0,1) := by
    simpa [A] using add_pos_of_nonneg_of_pos hv hε
  have hbound (q : H × ℝ) (hq : f q.1 ≤ (q.2 : EReal)) : b+ε*c < (L+ε • A) q := by
    have h1 := hb q hq
    have h2 := mul_le_mul_of_nonneg_left (hA q hq) hε.le
    change b+ε*c < L q+ε*A q
    linarith
  obtain ⟨l',c',hm,ht⟩ := positive_separator_affine f hf.1 (L+ε • A) (b+ε*c) hpos hbound
  exact ⟨l',c',hm,ht x r (by linarith)⟩

end Queelius.MoreauChance

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency MeasureTheory Filter Topology

theorem conic_probability_inf {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2)) (x : H) :
    (⨅ (l : ℝ) (_ : 0 < l), probFunReg C h Φ μ ξ l x) = probFun K Φ μ ξ x := by
  letI : MeasurableSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := borel _
  letI : BorelSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := ⟨rfl⟩
  have hX : Measurable (fun ω => WithLp.toLp 2 (x,ξ ω)) := by
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => WithLp.toLp 2 (x,z)) := by fun_prop
    exact hc.measurable.comp hξ
  have hn := generator_nonempty K C hset.C_generates_polar
  have heq : (fun q => (realSupFun C h Φ q : EReal)) = supFun C h Φ := by
    funext q
    exact coe_realSupFun C h Φ hn hset.C_weakStarCompact q
  unfold probFunReg
  rw [← heq]
  rw [envelope_probability_inf μ (realSupFun C h Φ) (realSupFun_convex K C h Φ hset)
    (realSupFun_lsc K C h Φ hset hΦ) _ hX (h x)]
  unfold probFun
  congr 1
  ext ω
  rw [Set.mem_setOf_eq,Set.mem_setOf_eq,← EReal.coe_le_coe_iff,
    coe_realSupFun C h Φ hn hset.C_weakStarCompact]
  exact (conic_event_equivalence K C h Φ hset x (ξ ω)).symm

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem theorem_3_1_a
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2)) (x : H) :
    (∀ l1 l2 : ℝ, 0 < l2 → l2 < l1 → probFunReg C h Φ μ ξ l2 x ≤ probFunReg C h Φ μ ξ l1 x) ∧
      (⨅ (l : ℝ) (_ : 0 < l), probFunReg C h Φ μ ξ l x) = probFun K Φ μ ξ x := by
  exact ⟨fun l1 l2 hl2 hle => Queelius.MoreauChance.probability_parameter_mono C h Φ μ ξ l1 l2 hl2 hle.le x,
    Queelius.MoreauChance.conic_probability_inf μ ξ hξ K C h Φ hset hΦ x⟩

end MoreauChance.Consistency

end

section
noncomputable section
namespace Queelius.MoreauChance
open MeasureTheory Filter Topology
open scoped ENNReal

theorem limsup_event_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω) (B : Set Ω)
    (hm : ∀ n, MeasurableSet (A n))
    (hexclude : ∀ ω ∉ B, ∀ᶠ n in atTop, ω ∉ A n) :
    limsup (fun n => μ (A n)) atTop ≤ μ B := by
  let tail : ℕ → Set Ω := fun n => ⋃ k ≥ n, A k
  have ht : ∀ n, MeasurableSet (tail n) := by
    intro n
    exact MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun _ => hm k))
  have ha : Antitone tail := by
    intro a b hab ω hω
    rcases Set.mem_iUnion.mp hω with ⟨k,hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hbk,hωk⟩
    exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hab.trans hbk,hωk⟩⟩
  have hlim := tendsto_measure_iInter_atTop (fun n => (ht n).nullMeasurableSet) ha
    ⟨0,measure_ne_top μ _⟩
  have hsub : (⋂ n, tail n) ⊆ B := by
    intro ω hω
    by_contra hb
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hexclude ω hb)
    have hw := Set.mem_iInter.mp hω N
    rcases Set.mem_iUnion.mp hw with ⟨k,hk⟩
    rcases Set.mem_iUnion.mp hk with ⟨hNk,hωk⟩
    exact hN k hNk hωk
  calc
    _ ≤ limsup (fun n => μ (tail n)) atTop := limsup_le_limsup (Filter.Eventually.of_forall (fun n =>
      measure_mono (fun ω hω => Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨le_rfl,hω⟩⟩)))
    _ = μ (⋂ n, tail n) := hlim.limsup_eq
    _ ≤ μ B := measure_mono hsub

end Queelius.MoreauChance

end

section
noncomputable section
namespace Queelius.MoreauChance
open MoreauChance.Consistency Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realEnvelope (g : E → ℝ) (lam : ℝ) (x : E) : ℝ := (moreauEnv (fun z => (g z : EReal)) lam x).toReal

theorem coe_realEnvelope (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) (x : E) :
    (realEnvelope g lam x : EReal) = moreauEnv (fun z => (g z : EReal)) lam x := by
  obtain ⟨L,c,hminor,htouch⟩ := ConvexOn.exists_affine_le_of_lt (𝕜:=ℝ)
    (s:=Set.univ) (φ:=g) (x:=(0 : E)) (a:=g 0-1) (Set.mem_univ _) (by linarith)
    isClosed_univ (hgl.lowerSemicontinuousOn Set.univ) hg
  have hm (z : E) : L z+c ≤ g z := by simpa using hminor ⟨z,Set.mem_univ z⟩
  apply EReal.coe_toReal
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top (g x)) (envelope_le _ lam x)
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (affine_lower_envelope g L c hm lam hp x)

theorem realEnvelope_le_cost (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) (x z : E) :
    realEnvelope g lam x ≤ g z+‖x-z‖^2/(2*lam) := by
  rw [← EReal.coe_le_coe_iff,coe_realEnvelope g hg hgl lam hp,EReal.coe_add]
  exact iInf_le _ z

theorem envelope_approximate_minimizer (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ z, g z+‖x-z‖^2/(2*lam) < realEnvelope g lam x+ε := by
  have he : moreauEnv (fun z => (g z : EReal)) lam x < ((realEnvelope g lam x+ε : ℝ) : EReal) := by
    rw [← coe_realEnvelope g hg hgl lam hp]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  simpa only [moreauEnv,iInf_lt_iff,← EReal.coe_add,EReal.coe_lt_coe_iff] using he

theorem realEnvelope_convex (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) :
    ConvexOn ℝ Set.univ (realEnvelope g lam) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨z,hz⟩ := envelope_approximate_minimizer g hg hgl lam hp x ε hε
  obtain ⟨w,hw⟩ := envelope_approximate_minimizer g hg hgl lam hp y ε hε
  have hnorm := ((convexOn_univ_norm (E:=E)).pow (fun _ _ => norm_nonneg _) 2).2
    (Set.mem_univ (x-z)) (Set.mem_univ (y-w)) ha hb hab
  have hdiff : a • x+b • y-(a • z+b • w) = a • (x-z)+b • (y-w) := by module
  have hcost := realEnvelope_le_cost g hg hgl lam hp (a • x+b • y) (a • z+b • w)
  have hgc := hg.2 (Set.mem_univ z) (Set.mem_univ w) ha hb hab
  rw [hdiff] at hcost
  simp only [smul_eq_mul] at hgc hnorm ⊢
  have hn := div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ 2*lam)
  have hza := mul_le_mul_of_nonneg_left hz.le ha
  have hwb := mul_le_mul_of_nonneg_left hw.le hb
  have heps : a*ε+b*ε=ε := by nlinarith [hab]
  dsimp at hn
  rw [add_div,mul_div_assoc,mul_div_assoc] at hn
  nlinarith

theorem realEnvelope_usc (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) :
    UpperSemicontinuous (realEnvelope g lam) := by
  intro x r hr
  have he : moreauEnv (fun z => (g z : EReal)) lam x < (r : EReal) := by
    rw [← coe_realEnvelope g hg hgl lam hp]
    exact EReal.coe_lt_coe_iff.mpr hr
  filter_upwards [(envelope_usc g lam) x (r : EReal) he] with y hy
  rw [← coe_realEnvelope g hg hgl lam hp] at hy
  exact EReal.coe_lt_coe_iff.mp hy

theorem realEnvelope_continuous (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (hgl : LowerSemicontinuous g) (lam : ℝ) (hp : 0 < lam) :
    Continuous (realEnvelope g lam) := by
  have hc := realEnvelope_convex g hg hgl lam hp
  have hus := realEnvelope_usc g hg hgl lam hp
  have he : (𝓝 (0 : E)).IsBoundedUnder (· ≤ ·) (realEnvelope g lam) := by
    refine ⟨realEnvelope g lam 0+1,?_⟩
    exact (hus 0 _ (by linarith)).mono (fun _ h => h.le)
  apply continuousOn_univ.mp
  apply ((hc.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp
  exact ⟨0,Set.mem_univ _,he⟩

end Queelius.MoreauChance

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem ereal_affine_lower_envelope (f : H → EReal) (L : H →L[ℝ] ℝ) (c : ℝ)
    (hminor : ∀ z, ((L z+c : ℝ) : EReal) ≤ f z) (lam : ℝ) (hlam : 0 < lam) (x : H) :
    ((L x+c-lam*‖L‖^2/2 : ℝ) : EReal) ≤ moreauEnv f lam x := by
  have h := affine_lower_envelope (fun z => L z+c) L c (fun _ => le_rfl) lam hlam x
  exact h.trans (envelope_mono_function _ f hminor lam x)

theorem gamma_envelope_finite (f : H → EReal) (hf : IsGammaZero f)
    (lam : ℝ) (hp : 0 < lam) (x : H) : moreauEnv f lam x ≠ ⊥ ∧ moreauEnv f lam x ≠ ⊤ := by
  obtain ⟨L,c,hminor⟩ := gamma_has_affine_minorant f hf
  constructor
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      (ereal_affine_lower_envelope f L c hminor lam hp x)
  · obtain ⟨z,hz⟩ := hf.2.1
    apply ne_top_of_le_ne_top _ (iInf_le _ z)
    exact EReal.add_ne_top hz (EReal.coe_ne_top _)

theorem gamma_envelope_tendsto (f : H → EReal) (hf : IsGammaZero f) (x : H) :
    Tendsto (fun l => moreauEnv f l x) (𝓝[>] 0) (𝓝 (f x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,har,hr⟩ := EReal.exists_rat_btwn_of_lt ha
    obtain ⟨L,c,hminor,htouch⟩ := gamma_affine_support_below f hf x (r : ℝ) hr
    have hcont : Continuous (fun l : ℝ => ((L x+c-l*‖L‖^2/2 : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    have hlim : Tendsto (fun l : ℝ => ((L x+c-l*‖L‖^2/2 : ℝ) : EReal))
        (𝓝[>] 0) (𝓝 ((L x+c : ℝ) : EReal)) := by
      simpa using (hcont.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0)
    have halt : a < ((L x+c : ℝ) : EReal) := har.trans (EReal.coe_lt_coe_iff.mpr htouch)
    filter_upwards [hlim.eventually (eventually_gt_nhds halt),self_mem_nhdsWithin] with l hl hlpos
    exact hl.trans_le (ereal_affine_lower_envelope f L c hminor l hlpos x)
  · intro b hb
    exact Filter.Eventually.of_forall (fun l => (envelope_le f l x).trans_lt hb)

theorem gamma_envelope_weak_liminf [CompleteSpace H]
    (f : H → EReal) (hf : IsGammaZero f) (xk : ℕ → H) (x : H) (lamk : ℕ → ℝ)
    (hxk : WeakConv xk x) (hlam_pos : ∀ k, 0 < lamk k)
    (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    f x ≤ liminf (fun k => moreauEnv f (lamk k) (xk k)) atTop := by
  rw [le_liminf_iff]
  intro a ha
  obtain ⟨r,har,hr⟩ := EReal.exists_rat_btwn_of_lt ha
  obtain ⟨L,c,hminor,htouch⟩ := gamma_affine_support_below f hf x (r : ℝ) hr
  have hreal : Tendsto (fun k => L (xk k)+c-lamk k*‖L‖^2/2) atTop (𝓝 (L x+c)) := by
    simpa using ((weakConv_dual_tendsto xk x hxk L).add_const c).sub
      ((hlam_lim.mul_const (‖L‖^2)).div_const 2)
  have hlim := (continuous_coe_real_ereal.tendsto (L x+c)).comp hreal
  have halt : a < ((L x+c : ℝ) : EReal) := har.trans (EReal.coe_lt_coe_iff.mpr htouch)
  filter_upwards [hlim.eventually (eventually_gt_nhds halt)] with k hk
  exact hk.trans_le (ereal_affine_lower_envelope f L c hminor (lamk k) (hlam_pos k) (xk k))

end Queelius.MoreauChance

end

section
noncomputable section
namespace Queelius.MoreauChance.Controls
open MoreauChance.Consistency MeasureTheory
open scoped ENNReal

theorem atomic_boundary_control (lam : ℝ) (hp : 0 < lam) :
    Measure.dirac (1 : ℝ) {ω | moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) lam ω ≤ (1 : EReal)} = 1 ∧
      Measure.dirac (1 : ℝ) {ω | ω^2 ≤ (1 : ℝ)} = 1 ∧
      Measure.dirac (1 : ℝ) {ω | ω^2 < (1 : ℝ)} = 0 := by
  constructor
  · apply Measure.dirac_apply_of_mem
    rw [Set.mem_setOf_eq,quadratic_envelope lam 1 hp]
    apply EReal.coe_le_coe_iff.mpr
    norm_num only [one_pow]
    apply (div_le_iff₀ (by linarith : 0 < 1+2*lam)).mpr
    linarith
  · constructor
    · apply Measure.dirac_apply_of_mem
      norm_num
    · norm_num [Measure.dirac_apply]

theorem zero_threshold_relaxation (lam : ℝ) (hp : 0 < lam) :
    {x : ℝ | moreauEnv (fun z : ℝ => ((z^2 : ℝ) : EReal)) lam x ≤ 0} = {0} := by
  ext x
  rw [Set.mem_setOf_eq,quadratic_envelope lam x hp]
  have hd : 0 < 1+2*lam := by linarith
  change ((x^2/(1+2*lam) : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) ↔ x = 0
  rw [EReal.coe_le_coe_iff,div_le_iff₀ hd]
  simp only [zero_mul]
  constructor
  · intro hx; nlinarith [sq_nonneg x]
  · intro hx; subst x; norm_num

end Queelius.MoreauChance.Controls

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem weakConv_prod_const {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (xk : ℕ → H) (x : H) (hx : WeakConv xk x) (z : F) :
    WeakConv (fun k => WithLp.toLp 2 (xk k,z)) (WithLp.toLp 2 (x,z)) := by
  intro y
  simpa only [WithLp.prod_inner_apply,WithLp.ofLp_toLp] using
    (hx (WithLp.ofLp y).1).add_const (inner ℝ z (WithLp.ofLp y).2)

theorem strong_implies_weak {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xk : ℕ → H) (x : H) (hx : Tendsto xk atTop (𝓝 x)) : WeakConv xk x := by
  intro y
  exact ((continuous_id.inner continuous_const).tendsto x).comp hx

theorem eventually_envelope_gt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (hg : ConvexOn ℝ Set.univ g) (hgl : LowerSemicontinuous g)
    (xk : ℕ → H) (x : H) (hx : WeakConv xk x) (lam : ℕ → ℝ)
    (hp : ∀ n, 0 < lam n) (hl : Tendsto lam atTop (𝓝 0))
    (r : ℕ → ℝ) (r0 : ℝ) (hr : Tendsto r atTop (𝓝 r0)) (hlt : r0 < g x) :
    ∀ᶠ n in atTop, (r n : EReal) < moreauEnv (fun z => (g z : EReal)) (lam n) (xk n) := by
  obtain ⟨c,hrc,hcg⟩ := exists_between hlt
  have he : (c : EReal) < liminf (fun n => moreauEnv (fun z => (g z : EReal)) (lam n) (xk n)) atTop :=
    (EReal.coe_lt_coe_iff.mpr hcg).trans_le (envelope_weak_liminf g hg hgl xk x lam hx hp hl)
  filter_upwards [eventually_lt_of_lt_liminf he,hr.eventually (eventually_lt_nhds hrc)] with n hn hrn
  exact (EReal.coe_lt_coe_iff.mpr hrn).trans hn

theorem conic_probability_limsup {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (lam : ℕ → ℝ) (hp : ∀ n, 0 < lam n) (hl : Tendsto lam atTop (𝓝 0))
    (xk : ℕ → H) (x : H) (hx : WeakConv xk x)
    (hh : Tendsto (fun n => h (xk n)) atTop (𝓝 (h x))) :
    limsup (fun n => probFunReg C h Φ μ ξ (lam n) (xk n)) atTop ≤ probFun K Φ μ ξ x := by
  letI : MeasurableSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := borel _
  letI : BorelSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := ⟨rfl⟩
  have hn := generator_nonempty K C hset.C_generates_polar
  have heq : (fun q => (realSupFun C h Φ q : EReal)) = supFun C h Φ := by
    funext q
    exact coe_realSupFun C h Φ hn hset.C_weakStarCompact q
  unfold probFunReg probFun
  rw [← heq]
  apply limsup_event_measure_le
  · intro n
    apply envelope_event_measurable
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => WithLp.toLp 2 (xk n,z)) := by fun_prop
    exact hc.measurable.comp hξ
  · intro ω hω
    have hgt : h x < realSupFun C h Φ (WithLp.toLp 2 (x,ξ ω)) := by
      apply lt_of_not_ge
      intro hh
      apply hω
      apply (conic_event_equivalence K C h Φ hset x (ξ ω)).mpr
      rw [← coe_realSupFun C h Φ hn hset.C_weakStarCompact]
      exact EReal.coe_le_coe_iff.mpr hh
    filter_upwards [eventually_envelope_gt (realSupFun C h Φ) (realSupFun_convex K C h Φ hset)
      (realSupFun_lsc K C h Φ hset hΦ) _ _ (weakConv_prod_const xk x hx (ξ ω)) lam hp hl
      (fun n => h (xk n)) (h x) hh hgt] with n hn
    exact not_le_of_gt hn

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem theorem_3_1_b
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (lamk : ℕ → ℝ) (hlam_pos : ∀ k, 0 < lamk k) (hlam_lim : Tendsto lamk atTop (𝓝 0))
    (xk : ℕ → H) (x : H) :
    (Tendsto xk atTop (𝓝 x) →
        limsup (fun k => probFunReg C h Φ μ ξ (lamk k) (xk k)) atTop ≤ probFun K Φ μ ξ x) ∧
      (SeqWeakCont h → WeakConv xk x →
        limsup (fun k => probFunReg C h Φ μ ξ (lamk k) (xk k)) atTop ≤ probFun K Φ μ ξ x) := by
  constructor
  · intro hx
    exact Queelius.MoreauChance.conic_probability_limsup μ ξ hξ K C h Φ hset hΦ lamk
      hlam_pos hlam_lim xk x (Queelius.MoreauChance.strong_implies_weak xk x hx)
      (hset.h_C1.continuous.tendsto x |>.comp hx)
  · intro hweak hx
    exact Queelius.MoreauChance.conic_probability_limsup μ ξ hξ K C h Φ hset hΦ lamk
      hlam_pos hlam_lim xk x hx (hweak xk x hx)

end MoreauChance.Consistency

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem gamma_coercive_bounded_below (f : H → EReal) (hf : IsGammaZero f)
    (hc : IsCoercive f) : ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x := by
  obtain ⟨L,c,hminor⟩ := gamma_has_affine_minorant f hf
  obtain ⟨R,hR⟩ := (hc 0).exists_norm_le
  refine ⟨min 0 (c-‖L‖*R),?_⟩
  intro x
  by_cases hx : f x ≤ 0
  · have hn := hR x hx
    have hL : -‖L‖*‖x‖ ≤ L x := by
      have h1 := L.le_opNorm x
      have h2 := neg_abs_le (L x)
      simp only [Real.norm_eq_abs] at h1
      linarith
    apply le_trans _ (hminor x)
    apply EReal.coe_le_coe_iff.mpr
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg L)
    exact (min_le_right _ _).trans (by linarith)
  · exact (EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans (le_of_not_ge hx)

theorem envelope_lower_bound (f : H → EReal) (b : ℝ) (hb : ∀ x, (b : EReal) ≤ f x)
    (lam : ℝ) (hp : 0 < lam) (x : H) : (b : EReal) ≤ moreauEnv f lam x := by
  rw [← envelope_constant b lam hp x]
  exact envelope_mono_function _ f hb lam x

theorem constrained_value_finite (f : H → EReal) (S : Set H)
    (hb : ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x)
    (hfeas : ∃ x ∈ S, f x ≠ ⊤) :
    (⨅ x ∈ S, f x) ≠ ⊥ ∧ (⨅ x ∈ S, f x) ≠ ⊤ := by
  obtain ⟨b,hb⟩ := hb
  obtain ⟨x,hx,hfinite⟩ := hfeas
  constructor
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (le_iInf fun x => le_iInf fun _ => hb x)
  · exact ne_top_of_le_ne_top hfinite (iInf_le_of_le x (iInf_le _ hx))

end Queelius.MoreauChance

end

section
noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace Queelius.MoreauChance
open MoreauChance.Consistency
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem bounded_sequence_weak_subsequence (x : ℕ → H) (R : ℝ) (hR : ∀ n, ‖x n‖ ≤ R) :
    ∃ (x0 : H) (φ : ℕ → ℕ), StrictMono φ ∧ WeakConv (x ∘ φ) x0 := by
  let f : ℕ → WeakDual ℝ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (x n))
  have hf (n : ℕ) : WeakDual.toStrongDual (f n) ∈ Metric.closedBall (0 : StrongDual ℝ H) R := by
    simpa [f,Metric.mem_closedBall,dist_zero_right] using hR n
  obtain ⟨u,hu,φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
  let x0 := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual u)
  refine ⟨x0,φ,hφ,?_⟩
  intro y
  have hy := ((WeakDual.eval_continuous y).tendsto u).comp ht
  have he : inner ℝ x0 y = u y := InnerProductSpace.toDual_symm_apply
  change Tendsto (fun n => inner ℝ (x (φ n)) y) atTop (𝓝 (u y)) at hy
  simpa only [Function.comp_apply,he] using hy

end Queelius.MoreauChance

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance.Controls
open MoreauChance.Consistency

def zeroIndicator (x : ℝ) : EReal := if x=0 then 0 else ⊤

theorem zeroIndicator_gamma : IsGammaZero zeroIndicator := by
  refine ⟨?_,⟨0,by simp [zeroIndicator]⟩,?_,?_⟩
  · intro x
    by_cases hx : x=0 <;> simp [zeroIndicator,hx]
  · have he : {q : ℝ × ℝ | zeroIndicator q.1 ≤ (q.2 : EReal)} =
        ({0} : Set ℝ) ×ˢ Set.Ici 0 := by
      ext q
      by_cases hq : q.1=0 <;> simp [zeroIndicator,hq]
    rw [he]
    exact (convex_singleton 0).prod (convex_Ici 0)
  · apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    by_cases ha : a=⊤
    · simp [ha]
    · by_cases h0 : (0 : EReal) ≤ a
      · have he : zeroIndicator ⁻¹' Set.Iic a = {0} := by
          ext x
          by_cases hx : x=0 <;> simp [zeroIndicator,hx,ha,h0]
        rw [he]
        exact isClosed_singleton
      · have he : zeroIndicator ⁻¹' Set.Iic a = ∅ := by
          ext x
          by_cases hx : x=0 <;> simp [zeroIndicator,hx,ha,h0]
        rw [he]
        exact isClosed_empty

theorem zeroIndicator_coercive : IsCoercive zeroIndicator := by
  intro a
  apply (Bornology.isBounded_singleton (x := (0 : ℝ))).subset
  intro x hx
  by_contra h
  have hne : x ≠ 0 := by simpa using h
  simpa [zeroIndicator,hne] using hx

theorem zeroIndicator_envelope (lam x : ℝ) :
    moreauEnv zeroIndicator lam x = ((‖x‖^2/(2*lam) : ℝ) : EReal) := by
  apply le_antisymm
  · exact (iInf_le _ (0 : ℝ)).trans_eq (by simp [zeroIndicator])
  · apply le_iInf
    intro z
    by_cases hz : z=0
    · simp [zeroIndicator,hz]
    · simp [zeroIndicator,hz]

theorem zeroIndicator_envelope_numeric : moreauEnv zeroIndicator 1 2 = 2 := by
  rw [zeroIndicator_envelope]
  norm_num
  rfl

theorem envelope_limit_outside_domain :
    Tendsto (fun lam => moreauEnv zeroIndicator lam 1) (𝓝[>] 0) (𝓝 ⊤) := by
  simpa [zeroIndicator] using gamma_envelope_tendsto zeroIndicator zeroIndicator_gamma 1

end Queelius.MoreauChance.Controls

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem eventual_lower_limsup {α : Type*} [CompleteLinearOrder α] (f : ℕ → α) (p : α)
    (hp : ∀ n, p ≤ f n) : p ≤ limsup f atTop := by
  exact (le_liminf_of_le (by isBoundedDefault) (Filter.Eventually.of_forall hp)).trans liminf_le_limsup

end Queelius.MoreauChance

namespace MoreauChance.Consistency

theorem proposition_5_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (lamk : ℕ → ℝ) (hlam_pos : ∀ k, 0 < lamk k) (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    PKConv (fun k => feasSetReg C h Φ μ ξ (lamk k) p) (feasSet K Φ μ ξ p) ∧
      (SeqWeakCont h →
        MoscoConv (fun k => feasSetReg C h Φ μ ξ (lamk k) p) (feasSet K Φ μ ξ p)) := by
  have hin : feasSet K Φ μ ξ p ⊆ setLiminf (fun k => feasSetReg C h Φ μ ξ (lamk k) p) := by
    intro x hx
    exact ⟨fun _ => x,fun k => Queelius.MoreauChance.feasible_inclusion K C h Φ hset μ ξ (lamk k) p hx,
      tendsto_const_nhds⟩
  constructor
  · refine ⟨hin,?_⟩
    rintro x ⟨kn,xn,hkn,hxn,hx⟩
    have hup := (theorem_3_1_b μ ξ hξ hdens K C h Φ hset hΦ (fun n => lamk (kn n))
      (fun n => hlam_pos (kn n)) (hlam_lim.comp hkn) xn x).1 hx
    exact (Queelius.MoreauChance.eventual_lower_limsup _ (ENNReal.ofReal p) hxn).trans hup
  · intro hw
    refine ⟨hin,?_⟩
    rintro x ⟨kn,xn,hkn,hxn,hx⟩
    have hup := (theorem_3_1_b μ ξ hξ hdens K C h Φ hset hΦ (fun n => lamk (kn n))
      (fun n => hlam_pos (kn n)) (hlam_lim.comp hkn) xn x).2 hw hx
    exact (Queelius.MoreauChance.eventual_lower_limsup _ (ENNReal.ofReal p) hxn).trans hup

end MoreauChance.Consistency

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem eventually_function_gt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (hg : ConvexOn ℝ Set.univ g) (hgl : LowerSemicontinuous g)
    (xk : ℕ → H) (x : H) (hx : WeakConv xk x)
    (r : ℕ → ℝ) (r0 : ℝ) (hr : Tendsto r atTop (𝓝 r0)) (hlt : r0 < g x) :
    ∀ᶠ n in atTop, r n < g (xk n) := by
  have hp (n : ℕ) : 0 < 1 / ((n : ℝ)+1) := by positivity
  filter_upwards [eventually_envelope_gt g hg hgl xk x hx (fun n => 1 / ((n : ℝ)+1)) hp
    tendsto_one_div_add_atTop_nhds_zero_nat r r0 hr hlt] with n hn
  exact EReal.coe_lt_coe_iff.mp (hn.trans_le (envelope_le (fun z => (g z : EReal)) _ _))

theorem probability_weak_usc {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : E → ℝ)
    (hg : ConvexOn ℝ Set.univ g) (hgl : LowerSemicontinuous g)
    (Xk : ℕ → Ω → E) (X : Ω → E) (hXm : ∀ n, Measurable (Xk n))
    (hX : ∀ ω, WeakConv (fun n => Xk n ω) (X ω))
    (r : ℕ → ℝ) (r0 : ℝ) (hr : Tendsto r atTop (𝓝 r0)) :
    limsup (fun n => μ {ω | g (Xk n ω) ≤ r n}) atTop ≤ μ {ω | g (X ω) ≤ r0} := by
  apply limsup_event_measure_le
  · intro n
    exact measurableSet_le (hgl.measurable.comp (hXm n)) measurable_const
  · intro ω hω
    have hh : r0 < g (X ω) := lt_of_not_ge hω
    filter_upwards [eventually_function_gt g hg hgl _ _ (hX ω) r r0 hr hh] with n hn
    exact not_le_of_gt hn

end Queelius.MoreauChance

end

section
noncomputable section
open Filter Topology
namespace Queelius.MoreauChance
open MoreauChance.Consistency
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem gamma_envelope_coercive (f : H → EReal) (hf : IsGammaZero f)
    (hc : IsCoercive f) (lam : ℝ) (hp : 0 < lam) : IsCoercive (moreauEnv f lam) := by
  obtain ⟨b,hb⟩ := gamma_coercive_bounded_below f hf hc
  intro a
  obtain ⟨R,hR⟩ := (hc (a+1)).exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R+Real.sqrt (2*lam*(a+1-b)),?_⟩
  intro x hx
  have hx' : moreauEnv f lam x < ((a+1 : ℝ) : EReal) :=
    hx.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨z,hz⟩ := iInf_lt_iff.mp hx'
  have hnonneg : (0 : EReal) ≤ ((‖x-z‖^2/(2*lam) : ℝ) : EReal) := by
    exact EReal.coe_le_coe_iff.mpr (by positivity)
  have hfa : f z < ((a+1 : ℝ) : EReal) :=
    (le_add_of_nonneg_right hnonneg).trans_lt hz
  have hnormz : ‖z‖ ≤ R := hR z hfa.le
  have hcost : b+‖x-z‖^2/(2*lam) < a+1 := by
    apply EReal.coe_lt_coe_iff.mp
    rw [EReal.coe_add]
    exact (add_le_add (hb z) le_rfl).trans_lt hz
  have hsq : ‖x-z‖^2 ≤ 2*lam*(a+1-b) := by
    have hlt : ‖x-z‖^2/(2*lam) < a+1-b := by linarith
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*lam)).mp hlt
    nlinarith
  have hdist : ‖x-z‖ ≤ Real.sqrt (2*lam*(a+1-b)) :=
    (Real.le_sqrt (norm_nonneg _) (by nlinarith [sq_nonneg ‖x-z‖])).mpr hsq
  have ht : ‖x‖ ≤ ‖x-z‖+‖z‖ := by simpa using norm_add_le (x-z) z
  linarith

end Queelius.MoreauChance

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem weak_optimal_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ψ : H → EReal) (hψ : IsGammaZero ψ) (hψ_coercive : IsCoercive ψ)
    (hfeas : (feasSet K Φ μ ξ p ∩ {x | ψ x ≠ ⊤}).Nonempty) :
    ∀ (lamk : ℕ → ℝ) (xk : ℕ → H) (x0 : H), (∀ k, 0 < lamk k) →
      Tendsto lamk atTop (𝓝 0) →
      (∀ k, IsOptimalPReg ψ C h Φ μ ξ (lamk k) p (xk k)) → WeakConv xk x0 →
      IsOptimalP ψ K Φ μ ξ p x0 := by
  intro lamk xk x0 hpos hlam hopt hx
  have hmosco := (proposition_5_1 μ ξ hξ hdens K C h Φ hset hΦ p hp lamk hpos hlam).2 h_weak
  have hfeasible : x0 ∈ feasSet K Φ μ ξ p :=
    hmosco.2 ⟨id,xk,tendsto_id,fun k => (hopt k).1,hx⟩
  refine ⟨hfeasible,?_⟩
  intro y hy
  have hlower := gamma_envelope_weak_liminf ψ hψ xk x0 lamk hx hpos hlam
  have hub (k : ℕ) : moreauEnv ψ (lamk k) (xk k) ≤ ψ y :=
    ((hopt k).2 y (feasible_inclusion K C h Φ hset μ ξ (lamk k) p hy)).trans
      (envelope_le ψ (lamk k) y)
  apply hlower.trans
  apply liminf_le_of_le (by isBoundedDefault)
  intro b hb
  obtain ⟨k,hk⟩ := hb.exists
  exact hk.trans (hub k)

end Queelius.MoreauChance

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem values_finite
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ψ : H → EReal) (hψ : IsGammaZero ψ) (hψ_coercive : IsCoercive ψ)
    (hfeas : (feasSet K Φ μ ξ p ∩ {x | ψ x ≠ ⊤}).Nonempty) :
    valP ψ K Φ μ ξ p ≠ ⊥ ∧ valP ψ K Φ μ ξ p ≠ ⊤ ∧
      (∀ lam : ℝ, 0 < lam → valPReg ψ C h Φ μ ξ lam p ≠ ⊥ ∧
        valPReg ψ C h Φ μ ξ lam p ≠ ⊤) := by
  have hb := gamma_coercive_bounded_below ψ hψ hψ_coercive
  obtain ⟨y,hy,hyf⟩ := hfeas
  have hbase := constrained_value_finite ψ (feasSet K Φ μ ξ p) hb ⟨y,hy,hyf⟩
  refine ⟨hbase.1,hbase.2,?_⟩
  intro lam hl
  apply constrained_value_finite (moreauEnv ψ lam) (feasSetReg C h Φ μ ξ lam p)
  · obtain ⟨b,hb⟩ := hb
    exact ⟨b,envelope_lower_bound ψ b hb lam hl⟩
  · exact ⟨y,feasible_inclusion K C h Φ hset μ ξ lam p hy,(gamma_envelope_finite ψ hψ lam hl y).2⟩

end Queelius.MoreauChance

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_3_1_d
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h) :
    (∀ (xk : ℕ → H) (x : H), WeakConv xk x →
        limsup (fun k => probFun K Φ μ ξ (xk k)) atTop ≤ probFun K Φ μ ξ x) ∧
      (∀ l : ℝ, 0 < l → ∀ (xk : ℕ → H) (x : H), WeakConv xk x →
        limsup (fun k => probFunReg C h Φ μ ξ l (xk k)) atTop ≤ probFunReg C h Φ μ ξ l x) := by
  constructor
  · intro xk x hx
    let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
    have hp (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
    calc
      _ ≤ limsup (fun n => probFunReg C h Φ μ ξ (lam n) (xk n)) atTop :=
        limsup_le_limsup (Filter.Eventually.of_forall (fun n =>
          Queelius.MoreauChance.probability_le_regularized K C h Φ hset μ ξ (lam n) (xk n)))
      _ ≤ probFun K Φ μ ξ x := Queelius.MoreauChance.conic_probability_limsup μ ξ hξ K C h Φ hset hΦ
        lam hp tendsto_one_div_add_atTop_nhds_zero_nat xk x hx (h_weak xk x hx)
  · intro lam hp xk x hx
    letI : MeasurableSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := borel _
    letI : BorelSpace (WithLp 2 (H × EuclideanSpace ℝ (Fin m))) := ⟨rfl⟩
    let G := Queelius.MoreauChance.realSupFun C h Φ
    have hGc := Queelius.MoreauChance.realSupFun_convex K C h Φ hset
    have hGl := Queelius.MoreauChance.realSupFun_lsc K C h Φ hset hΦ
    have hn := Queelius.MoreauChance.generator_nonempty K C hset.C_generates_polar
    have heq : (fun q => (G q : EReal)) = supFun C h Φ := by
      funext q
      exact Queelius.MoreauChance.coe_realSupFun C h Φ hn hset.C_weakStarCompact q
    have hprob (v : H) : probFunReg C h Φ μ ξ lam v =
        μ {ω | Queelius.MoreauChance.realEnvelope G lam (WithLp.toLp 2 (v,ξ ω)) ≤ h v} := by
      unfold probFunReg
      rw [← heq]
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← EReal.coe_le_coe_iff,Queelius.MoreauChance.coe_realEnvelope G hGc hGl lam hp]
    simp_rw [hprob]
    apply Queelius.MoreauChance.probability_weak_usc μ (Queelius.MoreauChance.realEnvelope G lam)
      (Queelius.MoreauChance.realEnvelope_convex G hGc hGl lam hp)
      (Queelius.MoreauChance.realEnvelope_continuous G hGc hGl lam hp).lowerSemicontinuous
    · intro n
      have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => WithLp.toLp 2 (xk n,z)) := by fun_prop
      exact hc.measurable.comp hξ
    · intro ω
      exact Queelius.MoreauChance.weakConv_prod_const xk x hx (ξ ω)
    · exact h_weak xk x hx

end MoreauChance.Consistency

end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace Queelius.MoreauChance
open MoreauChance.Consistency

theorem value_convergence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ψ : H → EReal) (hψ : IsGammaZero ψ) (hψ_coercive : IsCoercive ψ)
    (hfeas : (feasSet K Φ μ ξ p ∩ {x | ψ x ≠ ⊤}).Nonempty) :
    Tendsto (fun lam => valPReg ψ C h Φ μ ξ lam p) (𝓝[>] 0) (𝓝 (valP ψ K Φ μ ξ p)) := by
  have hub (lam : ℝ) : valPReg ψ C h Φ μ ξ lam p ≤ valP ψ K Φ μ ξ p := by
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact (iInf_le_of_le y (iInf_le _ (feasible_inclusion K C h Φ hset μ ξ lam p hy))).trans
      (envelope_le ψ lam y)
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro lamk hlam
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_contra hn
    have hfreq : ∃ᶠ n in atTop, valPReg ψ C h Φ μ ξ (lamk n) p ≤ a := by
      simpa only [not_lt,Function.comp_def] using (Filter.not_eventually.mp hn)
    obtain ⟨r,har,hr⟩ := EReal.exists_rat_btwn_of_lt ha
    have hzero : Tendsto lamk atTop (𝓝 0) := hlam.mono_right nhdsWithin_le_nhds
    have hpos : ∀ᶠ n in atTop, 0 < lamk n := hlam.eventually self_mem_nhdsWithin
    have hsmall : ∀ᶠ n in atTop, lamk n ≤ 1 :=
      hzero.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨φ,hφ,hφspec⟩ := extraction_of_frequently_atTop (hfreq.and_eventually (hpos.and hsmall))
    have hchoice (n : ℕ) : ∃ x ∈ feasSetReg C h Φ μ ξ (lamk (φ n)) p,
        moreauEnv ψ (lamk (φ n)) x < ((r : ℝ) : EReal) := by
      have hv := (hφspec n).1.trans_lt har
      simpa only [valPReg,iInf_lt_iff,exists_prop] using hv
    choose x hx hcost using hchoice
    have hbound : Bornology.IsBounded {x : H | moreauEnv ψ 1 x ≤ ((r : ℝ) : EReal)} :=
      gamma_envelope_coercive ψ hψ hψ_coercive 1 (by norm_num) (r : ℝ)
    obtain ⟨R,hR⟩ := hbound.exists_norm_le
    have hxR (n : ℕ) : ‖x n‖ ≤ R := by
      apply hR
      exact (envelope_antitone_parameter ψ 1 (lamk (φ n)) (hφspec n).2.1
        (hφspec n).2.2 (x n)).trans (hcost n).le
    obtain ⟨x0,σ,hσ,hweak⟩ := bounded_sequence_weak_subsequence x R hxR
    have hlim : Tendsto (fun n => lamk (φ (σ n))) atTop (𝓝 0) :=
      (hzero.comp hφ.tendsto_atTop).comp hσ.tendsto_atTop
    have hp' (n : ℕ) : 0 < lamk (φ (σ n)) := (hφspec (σ n)).2.1
    have hmosco := (proposition_5_1 μ ξ hξ hdens K C h Φ hset hΦ p hp
      (fun n => lamk (φ (σ n))) hp' hlim).2 h_weak
    have hx0 : x0 ∈ feasSet K Φ μ ξ p :=
      hmosco.2 ⟨id,x ∘ σ,tendsto_id,fun n => hx (σ n),hweak⟩
    have hlow := gamma_envelope_weak_liminf ψ hψ (x ∘ σ) x0
      (fun n => lamk (φ (σ n))) hweak hp' hlim
    have hupper : liminf (fun n => moreauEnv ψ (lamk (φ (σ n))) ((x ∘ σ) n)) atTop ≤
        ((r : ℝ) : EReal) := by
      apply liminf_le_of_le (by isBoundedDefault)
      intro b hb
      obtain ⟨n,hn⟩ := hb.exists
      exact hn.trans (hcost (σ n)).le
    have hv : valP ψ K Φ μ ξ p ≤ ((r : ℝ) : EReal) :=
      (iInf_le_of_le x0 (iInf_le _ hx0)).trans (hlow.trans hupper)
    exact not_lt_of_ge hv hr
  · intro b hb
    exact Filter.Eventually.of_forall (fun n => (hub (lamk n)).trans_lt hb)

theorem value_consistency
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (h_weak : SeqWeakCont h)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ψ : H → EReal) (hψ : IsGammaZero ψ) (hψ_coercive : IsCoercive ψ)
    (hfeas : (feasSet K Φ μ ξ p ∩ {x | ψ x ≠ ⊤}).Nonempty) :
    valP ψ K Φ μ ξ p ≠ ⊥ ∧ valP ψ K Φ μ ξ p ≠ ⊤ ∧
      (∀ lam : ℝ, 0 < lam → valPReg ψ C h Φ μ ξ lam p ≠ ⊥ ∧
        valPReg ψ C h Φ μ ξ lam p ≠ ⊤) ∧
      Tendsto (fun lam => valPReg ψ C h Φ μ ξ lam p) (𝓝[>] 0) (𝓝 (valP ψ K Φ μ ξ p)) := by
  have hf := values_finite μ ξ hξ hdens K C h Φ hset hΦ h_weak p hp ψ hψ hψ_coercive hfeas
  exact ⟨hf.1,hf.2.1,hf.2.2,
    value_convergence μ ξ hξ hdens K C h Φ hset hΦ h_weak p hp ψ hψ hψ_coercive hfeas⟩

end Queelius.MoreauChance

end

universe audit_u0

theorem solution : (
  ∀ {H : Type audit_u0} [inst : NormedAddCommGroup H]
    [inst_1 : @InnerProductSpace Real H Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)]
    [@CompleteSpace H
        (@PseudoMetricSpace.toUniformSpace H
          (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)))]
    [@TopologicalSpace.SeparableSpace H
        (@UniformSpace.toTopologicalSpace H
          (@PseudoMetricSpace.toUniformSpace H
            (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))]
    (g : H → Real),
    @ConvexOn Real H Real Real.semiring Real.partialOrder
        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) Real.instAddCommMonoid
        Real.partialOrder
        (@SMulZeroClass.toSMul Real H
          (@AddZero.toZero H
            (@AddZeroClass.toAddZero H
              (@AddMonoid.toAddZeroClass H
                (@SubNegMonoid.toAddMonoid H
                  (@AddGroup.toSubNegMonoid H
                    (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst)))))))
          (@DistribSMul.toSMulZeroClass Real H
            (@AddMonoid.toAddZeroClass H
              (@SubNegMonoid.toAddMonoid H
                (@AddGroup.toSubNegMonoid H (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst)))))
            (@DistribMulAction.toDistribSMul Real H Real.instMonoid
              (@SubNegMonoid.toAddMonoid H
                (@AddGroup.toSubNegMonoid H (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst))))
              (@Module.toDistribMulAction Real H Real.semiring
                (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                (@NormedSpace.toModule Real H Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                  (@InnerProductSpace.toNormedSpace Real H Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))))))
        (@instSMulOfMul Real Real.instMul) (@Set.univ H) g →
      @LowerSemicontinuous H Real
          (@UniformSpace.toTopologicalSpace H
            (@PseudoMetricSpace.toUniformSpace H
              (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
          Real.instPreorder g →
        ∀ (x : H),
          And
            (∀ (l1 l2 : Real),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) l2 →
                @LT.lt Real Real.instLT l2 l1 →
                  @LE.le EReal (@Preorder.toLE EReal (@PartialOrder.toPreorder EReal instPartialOrderEReal))
                    (@MoreauChance.Consistency.moreauEnv H inst (fun (z : H) => Real.toEReal (g z)) l1 x)
                    (@MoreauChance.Consistency.moreauEnv H inst (fun (z : H) => Real.toEReal (g z)) l2 x))
            (And
              (∀ (l : Real),
                @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) l →
                  @LE.le EReal (@Preorder.toLE EReal (@PartialOrder.toPreorder EReal instPartialOrderEReal))
                    (@MoreauChance.Consistency.moreauEnv H inst (fun (z : H) => Real.toEReal (g z)) l x)
                    (Real.toEReal (g x)))
              (@Filter.Tendsto Real EReal
                (fun (l : Real) => @MoreauChance.Consistency.moreauEnv H inst (fun (z : H) => Real.toEReal (g z)) l x)
                (@nhdsWithin Real
                  (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                  (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                  (@Set.Ioi Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))))
                (@nhds EReal EReal.instTopologicalSpace (Real.toEReal (g x)))))
) := @MoreauChance.Consistency.proposition_2_1_a
