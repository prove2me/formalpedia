-- Prove2me | solution 1 for MoreauChance.Consistency.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T20:19:50.139547+00:00
-- url     : https://prove2.me/submissions/4807c8e8-091b-46b3-8e21-ec3ac035ac7e

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

section
/-!
Classical supporting-functional existence for everywhere-finite convex functions.
Alexander Richard Towell, with substantial OpenAI Codex assistance.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Towell.MoreauSubgradient

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Baire category supplies local boundedness for a finite lower-semicontinuous
convex function; convexity propagates it to continuity everywhere. -/
theorem continuous_of_convex_lsc [BaireSpace E] (f : E → ℝ)
    (hcv : ConvexOn ℝ univ f) (hlsc : LowerSemicontinuous f) : Continuous f := by
  let C : ℕ → Set E := fun n => {x | f x ≤ (n : ℝ)}
  have hclosed (n : ℕ) : IsClosed (C n) := hlsc.isClosed_preimage (n : ℝ)
  have hcover : (⋃ n, C n) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (f x)
    exact ⟨n, hn.le⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hbound : (𝓝 x).IsBoundedUnder (· ≤ ·) f := by
    refine ⟨(n : ℝ), ?_⟩
    change ∀ᶠ y in 𝓝 x, f y ≤ (n : ℝ)
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (interior_subset (s := C n) hy : y ∈ C n)
  have hsome : ∃ z ∈ (univ : Set E), (𝓝 z).IsBoundedUnder (· ≤ ·) f :=
    ⟨x, mem_univ x, hbound⟩
  have hcont : ContinuousOn f univ :=
    ((hcv.continuousOn_tfae isOpen_univ univ_nonempty).out 3 1).mp hsome
  exact continuousOn_univ.mp hcont

/-- A continuous convex function on a real normed space has a continuous
linear support at each point. No finite-dimensional assumption is used. -/
theorem exists_linear_support (f : E → ℝ) (hcv : ConvexOn ℝ univ f)
    (hcont : Continuous f) (x0 : E) :
    ∃ l : E →L[ℝ] ℝ, ∀ y, f x0 + l (y - x0) ≤ f y := by
  let A : Set (E × ℝ) := {p | f p.1 < p.2}
  have hA : Convex ℝ A := by
    simpa [A] using hcv.convex_strict_epigraph
  have hopen : IsOpen A := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hout : (x0, f x0) ∉ A := by simp [A]
  obtain ⟨L, hsep⟩ := geometric_hahn_banach_point_open hA hopen hout
  let c : ℝ := L (0, 1)
  have hL (y : E) (t : ℝ) : L (y, t) = L (y, 0) + t * c := by
    have hp : (y, t) = (y, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hp, map_add, map_smul]
    rfl
  have hc : 0 < c := by
    have hs := hsep (x0, f x0 + 1) (by simp [A])
    rw [hL x0 (f x0), hL x0 (f x0 + 1)] at hs
    linarith
  have hboundary (y : E) : L (x0, f x0) ≤ L (y, 0) + f y * c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hs := hsep (y, f y + ε / c) (by
      change f y < f y + ε / c
      exact lt_add_of_pos_right _ (div_pos hε hc))
    rw [hL y (f y + ε / c), add_mul, div_mul_cancel₀ ε (ne_of_gt hc)] at hs
    simpa only [add_assoc] using hs.le
  let a : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  refine ⟨- c⁻¹ • a, ?_⟩
  intro y
  have hb := hboundary y
  rw [hL x0 (f x0)] at hb
  have ha (z : E) : a z = L (z, 0) := rfl
  simp only [smul_apply, map_sub, smul_eq_mul, ha]
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    (f x0 + (-c⁻¹ * L (y, 0) - -c⁻¹ * L (x0, 0))) * c =
        f x0 * c - (L (y, 0) - L (x0, 0)) := by
      field_simp
      ring
    _ ≤ f y * c := by nlinarith

end Normed

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The vector-valued Hilbert-space support for an everywhere-finite convex
lower-semicontinuous real function. -/
theorem exists_subgradient_real (f : H → ℝ)
    (hcv : ConvexOn ℝ univ f) (hlsc : LowerSemicontinuous f) (x0 : H) :
    ∃ u : H, ∀ y, f x0 + ⟪u, y - x0⟫_ℝ ≤ f y := by
  obtain ⟨l, hl⟩ := exists_linear_support f hcv (continuous_of_convex_lsc f hcv hlsc) x0
  refine ⟨(InnerProductSpace.toDual ℝ H).symm l, ?_⟩
  intro y
  simpa only [InnerProductSpace.toDual_symm_apply] using hl y

/-- Exact constituent hypotheses of the receiving platform's finite-objective
Gamma-zero case, with both infinity exclusions visible. -/
theorem exists_subgradient_ereal (ψ : H → EReal)
    (hbot : ∀ x, ψ x ≠ ⊥) (htop : ∀ x, ψ x ≠ ⊤)
    (hcv : Convex ℝ {q : H × ℝ | ψ q.1 ≤ (q.2 : EReal)})
    (hlsc : LowerSemicontinuous ψ) (x0 : H) :
    ∃ u : H, ψ x0 ≠ ⊤ ∧
      ∀ y, ψ x0 + ((⟪u, y - x0⟫_ℝ : ℝ) : EReal) ≤ ψ y := by
  let f : H → ℝ := fun x => (ψ x).toReal
  have hcoe (x : H) : ((f x : ℝ) : EReal) = ψ x :=
    EReal.coe_toReal (htop x) (hbot x)
  have hrealcv : ConvexOn ℝ univ f := by
    apply convexOn_of_convex_epigraph
    have heq : {q : H × ℝ | q.1 ∈ (univ : Set H) ∧ f q.1 ≤ q.2} =
        {q : H × ℝ | ψ q.1 ≤ (q.2 : EReal)} := by
      ext q
      simp only [mem_ofPred_eq, mem_univ, true_and]
      rw [← hcoe q.1, EReal.coe_le_coe_iff]
    exact heq.symm ▸ hcv
  have hreallsc : LowerSemicontinuous f := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro b
    have heq : f ⁻¹' Iic b = ψ ⁻¹' Iic (b : EReal) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      rw [← hcoe x, EReal.coe_le_coe_iff]
    rw [heq]
    exact hlsc.isClosed_preimage _
  obtain ⟨u, hu⟩ := exists_subgradient_real f hrealcv hreallsc x0
  refine ⟨u, htop x0, ?_⟩
  intro y
  rw [← hcoe x0, ← hcoe y, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact hu y

#print axioms continuous_of_convex_lsc
#print axioms exists_linear_support
#print axioms exists_subgradient_real
#print axioms exists_subgradient_ereal

end Hilbert
end Towell.MoreauSubgradient

end

section
/-!
Classical duality support for a strong minimum. Alexander Richard Towell,
with substantial OpenAI Codex assistance. No novelty claim.
-/

open Filter Topology
open scoped InnerProductSpace

namespace Towell.Moreau

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A uniform first-order upper estimate on a dual majorant exposes a primal
point quantitatively. No convexity, completeness, or finite dimensionality is
assumed: all duality information is in `hbound` and `hcontact`. -/
theorem gap_controls_norm (f g : H → ℝ) (u x0 : H)
    (hbound : ∀ᶠ v in 𝓝 u, ∀ x, ⟪v, x⟫_ℝ - f x ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : HasFDerivAt g (innerSL ℝ x0) u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : H,
      δ * ‖x - x0‖ ≤ (f x - ⟪u, x⟫_ℝ - (f x0 - ⟪u, x0⟫_ℝ)) + δ * ε := by
  have he := Asymptotics.isLittleO_iff.1
    (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdiff) hε
  have hadd : Tendsto (fun w : H => u + w) (𝓝 0) (𝓝 u) := by
    simpa using (tendsto_const_nhds.add (tendsto_id : Tendsto (fun w : H => w) (𝓝 0) (𝓝 0)))
  have hnear : ∀ᶠ w in 𝓝 (0 : H), ∀ x, ⟪u + w, x⟫_ℝ - f x ≤ g (u + w) :=
    hadd.eventually hbound
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff.1 (he.and hnear)
  let δ := ρ / 2
  have hδ : 0 < δ := half_pos hρ
  refine ⟨δ, hδ, ?_⟩
  intro x
  have hgap : 0 ≤ f x - ⟪u, x⟫_ℝ - (f x0 - ⟪u, x0⟫_ℝ) := by
    have hb := hbound.self_of_nhds x
    linarith
  by_cases hx : x = x0
  · subst x
    simp only [sub_self, norm_zero, mul_zero]
    positivity
  have hnpos : 0 < ‖x - x0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  let w : H := (δ / ‖x - x0‖) • (x - x0)
  have hwn : ‖w‖ = δ := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hδ hnpos)]
    exact div_mul_cancel₀ δ (ne_of_gt hnpos)
  have hwi : ⟪w, x - x0⟫_ℝ = δ * ‖x - x0‖ := by
    dsimp [w]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hwsmall : dist w 0 < ρ := by rw [dist_zero_right, hwn]; exact half_lt_self hρ
  obtain ⟨hs, hdual⟩ := hsmall hwsmall
  have hup : g (u + w) ≤ g u + ⟪x0, w⟫_ℝ + ε * δ := by
    rw [innerSL_apply_apply, hwn] at hs
    have hl := le_trans (le_abs_self (g (u + w) - g u - ⟪x0, w⟫_ℝ)) hs
    linarith
  have hb := hdual x
  rw [inner_add_left] at hb
  rw [inner_sub_right] at hwi
  have hi0 : ⟪x0, w⟫_ℝ = ⟪w, x0⟫_ℝ := real_inner_comm _ _
  rw [hcontact] at hup
  nlinarith

/-- Local Fenchel domination and contact identify the derivative. Thus the
strong-minimum result does not need a separately assumed gradient formula. -/
theorem derivative_of_contact (f g : H → ℝ) (u x0 : H)
    (hbound : ∀ᶠ v in 𝓝 u, ∀ x, ⟪v, x⟫_ℝ - f x ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : DifferentiableAt ℝ g u) :
    HasFDerivAt g (innerSL ℝ x0) u := by
  have hmin : IsLocalMin (fun v => g v - ⟪x0, v⟫_ℝ) u := by
    filter_upwards [hbound] with v hv
    have hb := hv x0
    have hcu : ⟪u, x0⟫_ℝ = ⟪x0, u⟫_ℝ := real_inner_comm _ _
    have hcv : ⟪v, x0⟫_ℝ = ⟪x0, v⟫_ℝ := real_inner_comm _ _
    linarith
  have hz := hmin.hasFDerivAt_eq_zero
    (hdiff.hasFDerivAt.sub (innerSL ℝ x0).hasFDerivAt)
  have heq : fderiv ℝ g u = innerSL ℝ x0 := sub_eq_zero.mp hz
  exact heq ▸ hdiff.hasFDerivAt

/-- A sequence approaching the tilted primal minimum converges in norm to
its exposed point. This is a strong-minimum conclusion, not just uniqueness. -/
theorem tendsto_of_tilted_gap (f g : H → ℝ) (u x0 : H)
    (hbound : ∀ᶠ v in 𝓝 u, ∀ x, ⟪v, x⟫_ℝ - f x ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : HasFDerivAt g (innerSL ℝ x0) u)
    (x : ℕ → H)
    (hgap : Tendsto (fun n => f (x n) - ⟪u, x n⟫_ℝ -
      (f x0 - ⟪u, x0⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 x0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := gap_controls_norm f g u x0 hbound hcontact hdiff (half_pos hε)
  have he := hgap.eventually (gt_mem_nhds (mul_pos hδ (half_pos hε)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, ?_⟩
  intro n hn
  have h := hb (x n)
  have hlt := hN n hn
  rw [dist_eq_norm]
  nlinarith

/-- Differentiability and local Fenchel contact suffice for the full sequential
strong-minimum conclusion. The dual majorant need only be finite locally. -/
theorem tendsto_of_differentiable_contact (f g : H → ℝ) (u x0 : H)
    (hbound : ∀ᶠ v in 𝓝 u, ∀ x, ⟪v, x⟫_ℝ - f x ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : DifferentiableAt ℝ g u)
    (x : ℕ → H)
    (hgap : Tendsto (fun n => f (x n) - ⟪u, x n⟫_ℝ -
      (f x0 - ⟪u, x0⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 x0) :=
  tendsto_of_tilted_gap f g u x0 hbound hcontact
    (derivative_of_contact f g u x0 hbound hcontact hdiff) x hgap

/-- An extended-real dual majorant only needs to be finite near the contact
point. Its values outside that neighborhood are irrelevant. -/
theorem tendsto_of_ereal_contact (f : H → ℝ) (G : H → EReal) (u x0 : H)
    (hbound : ∀ v x, ((⟪v, x⟫_ℝ - f x : ℝ) : EReal) ≤ G v)
    (hcontact : G u = ((⟪u, x0⟫_ℝ - f x0 : ℝ) : EReal))
    (hfinite : ∀ᶠ v in 𝓝 u, G v ≠ ⊤)
    (hdiff : DifferentiableAt ℝ (fun v => (G v).toReal) u)
    (x : ℕ → H)
    (hgap : Tendsto (fun n => f (x n) - ⟪u, x n⟫_ℝ -
      (f x0 - ⟪u, x0⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 x0) := by
  apply tendsto_of_differentiable_contact f (fun v => (G v).toReal) u x0
      ?_ ?_ hdiff x hgap
  · filter_upwards [hfinite] with v hv
    intro y
    simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal (hbound v y) (EReal.coe_ne_bot _) hv
  · simp only [hcontact, EReal.toReal_coe]

/-- The classical Fenchel conjugate of a finite real function, retaining
positive infinity outside its effective domain. -/
noncomputable def realFenchel (f : H → ℝ) (v : H) : EReal :=
  ⨆ y, ((⟪v, y⟫_ℝ - f y : ℝ) : EReal)

/-- For an everywhere-finite extended-real objective, the real conjugate
used here equals the receiver's literal extended-real supremum formula. -/
theorem realFenchel_toReal_eq (ψ : H → EReal)
    (hfinite : ∀ y, ψ y ≠ ⊤ ∧ ψ y ≠ ⊥) (v : H) :
    realFenchel (fun y => (ψ y).toReal) v =
      ⨆ y, ((⟪v, y⟫_ℝ : ℝ) : EReal) - ψ y := by
  apply iSup_congr
  intro y
  rw [EReal.coe_sub, EReal.coe_toReal (hfinite y).1 (hfinite y).2]

/-- Convert the literal primal extended-real subgradient inequality under
its exact global finiteness hypotheses. -/
theorem subgradient_toReal (ψ : H → EReal)
    (hfinite : ∀ y, ψ y ≠ ⊤ ∧ ψ y ≠ ⊥) (u x0 : H)
    (hsub : ∀ y, ψ x0 + ((⟪u, y - x0⟫_ℝ : ℝ) : EReal) ≤ ψ y) :
    ∀ y, (ψ x0).toReal + ⟪u, y - x0⟫_ℝ ≤ (ψ y).toReal := by
  intro y
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_add,
    EReal.coe_toReal (hfinite x0).1 (hfinite x0).2,
    EReal.coe_toReal (hfinite y).1 (hfinite y).2]
  exact hsub y

/-- A real subgradient supplies Fenchel contact. -/
theorem realFenchel_contact (f : H → ℝ) (u x0 : H)
    (hsub : ∀ y, f x0 + ⟪u, y - x0⟫_ℝ ≤ f y) :
    realFenchel f u = ((⟪u, x0⟫_ℝ - f x0 : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro y
    apply EReal.coe_le_coe_iff.mpr
    have h := hsub y
    rw [inner_sub_right] at h
    linarith
  · exact le_iSup (fun y => ((⟪u, y⟫_ℝ - f y : ℝ) : EReal)) x0

/-- The same contact equality puts the primal point in the subdifferential
of its conjugate at `u`. This needs no biconjugacy theorem. The conclusion
is the explicit extended-real subgradient predicate used by the receiver. -/
theorem realFenchel_subgradient (f : H → ℝ) (u x0 : H)
    (hsub : ∀ y, f x0 + ⟪u, y - x0⟫_ℝ ≤ f y) :
    realFenchel f u ≠ ⊤ ∧ ∀ v,
      realFenchel f u + ((⟪x0, v - u⟫_ℝ : ℝ) : EReal) ≤ realFenchel f v := by
  have hc := realFenchel_contact f u x0 hsub
  refine ⟨by rw [hc]; exact EReal.coe_ne_top _, ?_⟩
  intro v
  calc
    realFenchel f u + ((⟪x0, v - u⟫_ℝ : ℝ) : EReal) =
        ((⟪v, x0⟫_ℝ - f x0 : ℝ) : EReal) := by
      rw [hc, ← EReal.coe_add]
      congr 1
      rw [inner_sub_right]
      have hu : ⟪x0, u⟫_ℝ = ⟪u, x0⟫_ℝ := real_inner_comm _ _
      have hv : ⟪x0, v⟫_ℝ = ⟪v, x0⟫_ℝ := real_inner_comm _ _
      linarith
    _ ≤ realFenchel f v := le_iSup (fun y => ((⟪v, y⟫_ℝ - f y : ℝ) : EReal)) x0

/-- Frechet differentiability of the conjugate at a subgradient yields a
strong minimum for the tilted primal function. Finiteness is local on the
conjugate side; no finite-dimensional or compactness hypothesis is hidden. -/
theorem tendsto_of_conjugate_differentiable (f : H → ℝ) (u x0 : H)
    (hsub : ∀ y, f x0 + ⟪u, y - x0⟫_ℝ ≤ f y)
    (hfinite : ∀ᶠ v in 𝓝 u, realFenchel f v ≠ ⊤)
    (hdiff : DifferentiableAt ℝ (fun v => (realFenchel f v).toReal) u)
    (x : ℕ → H)
    (hgap : Tendsto (fun n => f (x n) - ⟪u, x n⟫_ℝ -
      (f x0 - ⟪u, x0⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 x0) :=
  tendsto_of_ereal_contact f (realFenchel f) u x0
    (fun v y => le_iSup (fun z => ((⟪v, z⟫_ℝ - f z : ℝ) : EReal)) y)
    (realFenchel_contact f u x0 hsub) hfinite hdiff x hgap

#print axioms tendsto_of_ereal_contact
#print axioms subgradient_toReal
#print axioms realFenchel_toReal_eq
#print axioms realFenchel_subgradient
#print axioms realFenchel_contact
#print axioms tendsto_of_conjugate_differentiable

#print axioms derivative_of_contact
#print axioms tendsto_of_differentiable_contact

#print axioms gap_controls_norm
#print axioms tendsto_of_tilted_gap

end Towell.Moreau

end

section
open Filter Topology
open scoped InnerProductSpace

namespace Towell.MoreauProximal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A common lower objective bound and approximate Moreau costs force the
primal/approximate-proximal residual to vanish. No exact prox attainment needed. -/
theorem residual_tendsto_zero (f : H → ℝ) (b c : ℝ)
    (hb : ∀ y, b ≤ f y) (lam eps : ℕ → ℝ) (x z : ℕ → H)
    (hlam : ∀ n, 0 < lam n) (hlam0 : Tendsto lam atTop (𝓝 0))
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hcost : ∀ n, f (z n) + ‖x n - z n‖^2 / (2 * lam n) ≤ c + eps n) :
    Tendsto (fun n => x n - z n) atTop (𝓝 0) := by
  have hs (n : ℕ) : ‖x n - z n‖^2 ≤ (c + eps n - b) * (2 * lam n) := by
    have hd : ‖x n - z n‖^2 / (2 * lam n) ≤ c + eps n - b := by
      have := hcost n
      have := hb (z n)
      linarith
    exact (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hlam n))).mp hd
  have hlim : Tendsto (fun n => (c + eps n - b) * (2 * lam n)) atTop (𝓝 0) := by
    convert ((tendsto_const_nhds.add heps0).sub tendsto_const_nhds).mul
      (tendsto_const_nhds.mul hlam0) using 1 <;> simp
  have hsq : Tendsto (fun n => ‖x n - z n‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hs hlim
  have hn : Tendsto (fun n => ‖x n - z n‖) atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

/-- One weak pairing, a global supporting slope and the approximate cost
bound suffice for tilted-gap convergence. Weak lower semicontinuity and
exact proximal minimizers are not needed in this bridge. -/
theorem tilted_gap_tendsto_zero (f : H → ℝ) (b : ℝ) (u x0 : H)
    (hb : ∀ y, b ≤ f y)
    (hsub : ∀ y, f x0 + ⟪u, y - x0⟫_ℝ ≤ f y)
    (lam eps : ℕ → ℝ) (x z : ℕ → H)
    (hlam : ∀ n, 0 < lam n) (hlam0 : Tendsto lam atTop (𝓝 0))
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hpair : Tendsto (fun n => ⟪u, x n - x0⟫_ℝ) atTop (𝓝 0))
    (hcost : ∀ n, f (z n) + ‖x n - z n‖^2 / (2 * lam n) ≤ f x0 + eps n) :
    Tendsto (fun n => f (z n) - ⟪u, z n⟫_ℝ -
      (f x0 - ⟪u, x0⟫_ℝ)) atTop (𝓝 0) := by
  have hr := residual_tendsto_zero f b (f x0) hb lam eps x z hlam hlam0 heps0 hcost
  have hri : Tendsto (fun n => ⟪u, x n - z n⟫_ℝ) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((innerSL ℝ u).continuous.tendsto 0).comp hr
  have hpz : Tendsto (fun n => ⟪u, z n - x0⟫_ℝ) atTop (𝓝 0) := by
    have heq : (fun n => ⟪u, z n - x0⟫_ℝ) =
        (fun n => ⟪u, x n - x0⟫_ℝ - ⟪u, x n - z n⟫_ℝ) := by
      funext n
      simp only [inner_sub_right]
      ring
    rw [heq]
    simpa using hpair.sub hri
  apply squeeze_zero
  · intro n
    have := hsub (z n)
    rw [inner_sub_right] at this
    linarith
  · intro n
    have hc := hcost n
    have hp : 0 ≤ ‖x n - z n‖^2 / (2 * lam n) :=
      div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (hlam n).le)
    have hi : ⟪u, z n - x0⟫_ℝ = ⟪u, z n⟫_ℝ - ⟪u, x0⟫_ℝ := inner_sub_right _ _ _
    show f (z n) - ⟪u, z n⟫_ℝ - (f x0 - ⟪u, x0⟫_ℝ) ≤ eps n - ⟪u, z n - x0⟫_ℝ
    linarith
  · simpa using heps0.sub hpz

/-- Combine approximate Moreau costs with the previously verified local
Fenchel strong minimum. This is conditional on the displayed real cost and
pairing interfaces, not the complete chance-constrained optimization root. -/
theorem tendsto_of_approximate_cost (f g : H → ℝ) (b : ℝ) (u x0 : H)
    (hb : ∀ y, b ≤ f y)
    (hdual : ∀ᶠ v in 𝓝 u, ∀ y, ⟪v, y⟫_ℝ - f y ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : DifferentiableAt ℝ g u)
    (lam eps : ℕ → ℝ) (x z : ℕ → H)
    (hlam : ∀ n, 0 < lam n) (hlam0 : Tendsto lam atTop (𝓝 0))
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hpair : Tendsto (fun n => ⟪u, x n - x0⟫_ℝ) atTop (𝓝 0))
    (hcost : ∀ n, f (z n) + ‖x n - z n‖^2 / (2 * lam n) ≤ f x0 + eps n) :
    Tendsto x atTop (𝓝 x0) := by
  have hsub (y : H) : f x0 + ⟪u, y - x0⟫_ℝ ≤ f y := by
    have hh := hdual.self_of_nhds y
    rw [hcontact] at hh
    rw [inner_sub_right]
    linarith
  have hgap := tilted_gap_tendsto_zero f b u x0 hb hsub lam eps x z
    hlam hlam0 heps0 hpair hcost
  have hz := Towell.Moreau.tendsto_of_differentiable_contact f g u x0 hdual hcontact hdiff z hgap
  have hr := residual_tendsto_zero f b (f x0) hb lam eps x z hlam hlam0 heps0 hcost
  simpa using hr.add hz

/-- The literal extended-real infimum bound selects an approximate point.
This does not assume that the Moreau infimum is attained. -/
theorem exists_approximate_cost (f : H → ℝ) (lam : ℝ) (x : H) (c ε : ℝ)
    (heps : 0 < ε)
    (henv : (⨅ y, ((f y : ℝ) : EReal) +
      ((‖x-y‖^2 / (2*lam) : ℝ) : EReal)) ≤ (c : EReal)) :
    ∃ y, f y + ‖x-y‖^2 / (2*lam) ≤ c + ε := by
  have hlt : (⨅ y, ((f y : ℝ) : EReal) +
      ((‖x-y‖^2 / (2*lam) : ℝ) : EReal)) < ((c+ε : ℝ) : EReal) :=
    henv.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlt
  refine ⟨y, ?_⟩
  rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at hy
  exact hy.le

/-- From the actual EReal envelope upper bounds, one fixed weak pairing and
local differentiable Fenchel contact, the original sequence converges in norm.
Global lower boundedness is explicit; no exact proximal point is constructed. -/
theorem tendsto_of_envelope_bounds (f g : H → ℝ) (b : ℝ) (u x0 : H)
    (hb : ∀ y, b ≤ f y)
    (hdual : ∀ᶠ v in 𝓝 u, ∀ y, ⟪v, y⟫_ℝ - f y ≤ g v)
    (hcontact : g u = ⟪u, x0⟫_ℝ - f x0)
    (hdiff : DifferentiableAt ℝ g u)
    (lam : ℕ → ℝ) (x : ℕ → H)
    (hlam : ∀ n, 0 < lam n) (hlam0 : Tendsto lam atTop (𝓝 0))
    (hpair : Tendsto (fun n => ⟪u, x n - x0⟫_ℝ) atTop (𝓝 0))
    (henv : ∀ n, (⨅ y, ((f y : ℝ) : EReal) +
      ((‖x n-y‖^2 / (2*lam n) : ℝ) : EReal)) ≤ (f x0 : EReal)) :
    Tendsto x atTop (𝓝 x0) := by
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  choose z hz using (fun n => exists_approximate_cost f (lam n) (x n) (f x0)
    (eps n) (heps n) (henv n))
  exact tendsto_of_approximate_cost f g b u x0 hb hdual hcontact hdiff lam eps x z
    hlam hlam0 tendsto_one_div_add_atTop_nhds_zero_nat hpair hz

#print axioms exists_approximate_cost
#print axioms tendsto_of_envelope_bounds

#print axioms residual_tendsto_zero
#print axioms tilted_gap_tendsto_zero
#print axioms tendsto_of_approximate_cost

end Towell.MoreauProximal

end

section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem theorem_5_4
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
    (valP ψ K Φ μ ξ p ≠ ⊥ ∧ valP ψ K Φ μ ξ p ≠ ⊤ ∧
        (∀ lam : ℝ, 0 < lam →
          valPReg ψ C h Φ μ ξ lam p ≠ ⊥ ∧ valPReg ψ C h Φ μ ξ lam p ≠ ⊤) ∧
        Tendsto (fun lam => valPReg ψ C h Φ μ ξ lam p) (𝓝[>] 0) (𝓝 (valP ψ K Φ μ ξ p))) ∧
      (∀ (lamk : ℕ → ℝ) (xk : ℕ → H) (x0 : H), (∀ k, 0 < lamk k) →
        Tendsto lamk atTop (𝓝 0) →
        (∀ k, IsOptimalPReg ψ C h Φ μ ξ (lamk k) p (xk k)) → WeakConv xk x0 →
        IsOptimalP ψ K Φ μ ξ p x0 ∧
          ((∀ x, ψ x ≠ ⊤) →
            (∀ u, (subdiff (conj ψ) u).Nonempty → FrechetDiffAtE (conj ψ) u) →
            Tendsto xk atTop (𝓝 x0))) := by
  constructor
  · exact Queelius.MoreauChance.value_consistency μ ξ hξ hdens K C h Φ hset hΦ h_weak p hp ψ hψ hψ_coercive hfeas
  · intro lamk xk x0 hpos hlam hopt hx
    have hopt0 := Queelius.MoreauChance.weak_optimal_limit μ ξ hξ hdens K C h Φ hset hΦ h_weak p hp ψ hψ hψ_coercive hfeas lamk xk x0 hpos hlam hopt hx
    refine ⟨hopt0, ?_⟩
    intro hfinite hdiffall
    let f : H → ℝ := fun y => (ψ y).toReal
    have hfin (y : H) : ψ y ≠ ⊤ ∧ ψ y ≠ ⊥ := ⟨hfinite y, hψ.1 y⟩
    have hcoe (y : H) : ((f y : ℝ) : EReal) = ψ y := EReal.coe_toReal (hfinite y) (hψ.1 y)
    obtain ⟨u, hut, hus⟩ := Towell.MoreauSubgradient.exists_subgradient_ereal ψ hψ.1 hfinite hψ.2.2.1 hψ.2.2.2 x0
    have hsub := Towell.Moreau.subgradient_toReal ψ hfin u x0 hus
    have hconj : Towell.Moreau.realFenchel f = conj ψ := by
      funext v
      exact Towell.Moreau.realFenchel_toReal_eq ψ hfin v
    have hsd : x0 ∈ subdiff (conj ψ) u := by
      rw [← hconj]
      exact Towell.Moreau.realFenchel_subgradient f u x0 hsub
    have hcd := hdiffall u ⟨x0, hsd⟩
    obtain ⟨L, hL⟩ := hcd.2
    let g : H → ℝ := fun v => ((conj ψ) v).toReal
    obtain ⟨b, hb⟩ := Queelius.MoreauChance.gamma_coercive_bounded_below ψ hψ hψ_coercive
    have hfb (y : H) : b ≤ f y := by
      apply EReal.coe_le_coe_iff.mp
      rw [hcoe]
      exact hb y
    have hd : ∀ᶠ v in 𝓝 u, ∀ y, ⟪v, y⟫_ℝ - f y ≤ g v := by
      filter_upwards [hcd.1] with v hv
      intro y
      have hy : ((⟪v, y⟫_ℝ - f y : ℝ) : EReal) ≤ conj ψ v := by
        rw [← hconj]
        exact le_iSup (fun z => ((⟪v, z⟫_ℝ - f z : ℝ) : EReal)) y
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hy (EReal.coe_ne_bot _) hv.1
    have hc : g u = ⟪u, x0⟫_ℝ - f x0 := by
      dsimp [g]
      rw [← hconj, Towell.Moreau.realFenchel_contact f u x0 hsub, EReal.toReal_coe]
    apply Towell.MoreauProximal.tendsto_of_envelope_bounds f g b u x0 hfb hd hc hL.differentiableAt lamk xk hpos hlam
    · have hh : Tendsto (fun n => ⟪xk n, u⟫_ℝ - ⟪x0, u⟫_ℝ) atTop
          (𝓝 (⟪x0, u⟫_ℝ - ⟪x0, u⟫_ℝ)) := (hx u).sub tendsto_const_nhds
      simpa [inner_sub_right, real_inner_comm] using hh
    · intro n
      have he : moreauEnv ψ (lamk n) (xk n) ≤ ψ x0 :=
        ((hopt n).2 x0 (Queelius.MoreauChance.feasible_inclusion K C h Φ hset μ ξ (lamk n) p hopt0.1)).trans
          (Queelius.MoreauChance.envelope_le ψ (lamk n) x0)
      simp_rw [hcoe]
      exact he


end MoreauChance.Consistency

#print axioms MoreauChance.Consistency.theorem_5_4

end

open MeasureTheory Filter Topology MoreauChance.Consistency
open scoped InnerProductSpace ENNReal

theorem solution
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
    (valP ψ K Φ μ ξ p ≠ ⊥ ∧ valP ψ K Φ μ ξ p ≠ ⊤ ∧
        (∀ lam : ℝ, 0 < lam →
          valPReg ψ C h Φ μ ξ lam p ≠ ⊥ ∧ valPReg ψ C h Φ μ ξ lam p ≠ ⊤) ∧
        Tendsto (fun lam => valPReg ψ C h Φ μ ξ lam p) (𝓝[>] 0) (𝓝 (valP ψ K Φ μ ξ p))) ∧
      (∀ (lamk : ℕ → ℝ) (xk : ℕ → H) (x0 : H), (∀ k, 0 < lamk k) →
        Tendsto lamk atTop (𝓝 0) →
        (∀ k, IsOptimalPReg ψ C h Φ μ ξ (lamk k) p (xk k)) → WeakConv xk x0 →
        IsOptimalP ψ K Φ μ ξ p x0 ∧
          ((∀ x, ψ x ≠ ⊤) →
            (∀ u, (subdiff (conj ψ) u).Nonempty → FrechetDiffAtE (conj ψ) u) →
            Tendsto xk atTop (𝓝 x0))) := by
  exact MoreauChance.Consistency.theorem_5_4 μ ξ hξ hdens K C h Φ hset hΦ h_weak p hp ψ hψ hψ_coercive hfeas

