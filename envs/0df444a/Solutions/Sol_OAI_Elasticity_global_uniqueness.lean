-- Prove2me | solution 1 for OAI.Elasticity.global_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:01:11.214539+00:00
-- url     : https://prove2.me/submissions/b0b8394a-becb-40fc-a9be-572d2414bae3

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_Elasticity_dn_global_coefficients_equal
import Theorems.Thm_OAI_ElasticityBoundaryPacket_boundary_jets_global

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
attribute [local instance] Classical.propDecidable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_piecewise (s : Set E) (f g : E → F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hv : ∀ x ∈ frontier s, f x=g x)
    (hd : ∀ x ∈ frontier s, fderiv ℝ f x=fderiv ℝ g x) (x : E) :
    HasFDerivAt (s.piecewise f g) (s.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
  classical
  by_cases hb : x ∈ frontier s
  · have hvf : s.piecewise f g x=f x := by
      by_cases hx : x∈s
      · simp [hx]
      · simp [hx,hv x hb]
    have hvg : s.piecewise f g x=g x := hvf.trans (hv x hb)
    have hd' : s.piecewise (fderiv ℝ f) (fderiv ℝ g) x=fderiv ℝ f x := by
      by_cases hx : x∈s
      · simp [hx]
      · simp [hx,hd x hb]
    rw [hd']
    have h1 : HasFDerivWithinAt (s.piecewise f g) (fderiv ℝ f x) s x :=
      (hf x).hasFDerivAt.hasFDerivWithinAt.congr (by intro y hy; simp [hy]) hvf
    have h2 : HasFDerivWithinAt (s.piecewise f g) (fderiv ℝ f x) sᶜ x := by
      rw [hd x hb]
      exact (hg x).hasFDerivAt.hasFDerivWithinAt.congr (by intro y hy; exact piecewise_eq_of_notMem s f g hy) hvg
    simpa only [union_compl_self,hasFDerivWithinAt_univ] using h1.union h2
  · by_cases hx : x∈s
    · simp only [piecewise_eq_of_mem s _ _ hx]
      apply (hf x).hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [mem_interior_iff_mem_nhds.mp ((mem_interior_iff_notMem_frontier hx).mpr hb)] with y hy
      simp [hy]
    · simp only [piecewise_eq_of_notMem s _ _ hx]
      apply (hg x).hasFDerivAt.congr_of_eventuallyEq
      have hi : x∈interior sᶜ := (mem_interior_iff_notMem_frontier hx).mpr (by simpa using hb)
      filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
      exact piecewise_eq_of_notMem s f g hy

/-- Matching all actual Fréchet jets gives smooth gluing across an arbitrary interface. -/
theorem smooth_piecewise_all_jets (s : Set E) (f g : E → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hj : ∀ n : ℕ, ∀ x∈frontier s, iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x) :
    ContDiff ℝ (⊤ : ℕ∞) (s.piecewise f g) := by
  classical
  have main : ∀ n : ℕ, ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f g : E → F), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ m : ℕ, ∀ x∈frontier s, iteratedFDeriv ℝ m f x=iteratedFDeriv ℝ m g x) →
      ContDiff ℝ n (s.piecewise f g) := by
    intro n
    induction n with
    | zero =>
      intro F _ _ f g hf hg hj
      change ContDiff ℝ 0 _
      rw [contDiff_zero]
      apply Continuous.piecewise _ hf.continuous hg.continuous
      intro x hx
      have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hj 0 x hx)
      simpa using hh
    | succ n ih =>
      intro F _ _ f g hf hg hj
      have hd : ∀ m : ℕ, ∀ x∈frontier s,
          iteratedFDeriv ℝ m (fderiv ℝ f) x=iteratedFDeriv ℝ m (fderiv ℝ g) x := by
        intro m x hx
        have hh := hj (m+1) x hx
        simp only [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply] at hh
        exact (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.injective hh
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨s.piecewise (fderiv ℝ f) (fderiv ℝ g),
        ih _ _ _ (hf.fderiv_right (by simp)) (hg.fderiv_right (by simp)) hd, ?_⟩
      intro x
      apply hasFDerivAt_piecewise s f g (hf.differentiable (by simp)) (hg.differentiable (by simp))
      · intro y hy
        have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hj 0 y hy)
        simpa using hh
      · intro y hy
        have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hd 0 y hy)
        simpa using hh
  exact contDiff_infty.mpr (fun n => main n F f g hf hg hj)
end ElasticityBoundary

end
end
section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

omit [FiniteDimensional ℝ E] in
lemma contDiff_cutoff_mul {U : Set E} (hU : IsOpen U) (f χ : E → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ⊆U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x*f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈U
  · exact hχ.contDiffAt.mul ((hf x hx).contDiffAt (hU.mem_nhds hx))
  · have hn : x∉tsupport χ := fun hh => hx (hs hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

/-- A genuine global smooth extension, equal on a neighborhood of the compact set. -/
theorem smooth_global_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (f : E → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ F : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ F =ᶠ[𝓝ˢ K] f := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => χ x*f x,contDiff_cutoff_mul hU f χ hf hχ hs,?_,?_⟩
  · exact hc.mul_right
  · filter_upwards [h1] with x hx
    simp [hx]

/-- Convex interpolation preserves both physical positivity inequalities. -/
theorem admissible_global_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (lam mu : E → ℝ)
    (hl : ContDiffOn ℝ (⊤ : ℕ∞) lam U) (hm : ContDiffOn ℝ (⊤ : ℕ∞) mu U)
    (hp : ∀ x∈K, 0 < mu x ∧ 0<3*lam x+2*mu x) :
    ∃ L M : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) L ∧ ContDiff ℝ (⊤ : ℕ∞) M ∧
      L =ᶠ[𝓝ˢ K] lam ∧ M =ᶠ[𝓝ˢ K] mu ∧
      (∀ x,0 < M x ∧ 0<3*L x+2*M x) ∧
      HasCompactSupport L ∧ HasCompactSupport (fun x => M x-1) := by
  obtain ⟨f,hf,_,hfl⟩ := smooth_global_extension hK hU hKU lam hl
  obtain ⟨g,hg,_,hgm⟩ := smooth_global_extension hK hU hKU mu hm
  let V := {x | 0<g x} ∩ {x | 0<3*f x+2*g x}
  have hV : IsOpen V := (isOpen_lt continuous_const hg.continuous).inter
    (isOpen_lt continuous_const ((continuous_const.mul hf.continuous).add (continuous_const.mul hg.continuous)))
  have hKV : K⊆V := by
    intro x hx
    change 0<g x ∧ 0<3*f x+2*g x
    rw [hfl.self_of_nhdsSet hx,hgm.self_of_nhdsSet hx]
    exact hp x hx
  obtain ⟨χ,hχ,hc,hs,h1,hb⟩ := compact_smooth_cutoff hK hV hKV
  let L := fun x => χ x*f x
  let M := fun x => χ x*g x+(1-χ x)
  refine ⟨L,M,hχ.mul hf,(hχ.mul hg).add (contDiff_const.sub hχ),?_,?_,?_,?_,?_⟩
  · filter_upwards [h1,hfl] with x hx hy
    simp [L,hx,hy]
  · filter_upwards [h1,hgm] with x hx hy
    simp [M,hx,hy]
  · intro x
    by_cases hx : χ x=0
    · simp [L,M,hx]
    · have hv := hs (subset_tsupport χ (show χ x≠0 from hx))
      have hpos : 0<χ x := lt_of_le_of_ne (hb x).1 (Ne.symm hx)
      have hle := (hb x).2
      have hgpos := hv.1
      have hpair := hv.2
      change 0<χ x*g x+(1-χ x) ∧ 0<3*(χ x*f x)+2*(χ x*g x+(1-χ x))
      constructor
      · nlinarith [mul_pos hpos hgpos]
      · nlinarith [mul_pos hpos hpair]
  · exact hc.mul_right
  · have he : (fun x => M x-1)=(fun x => χ x*(g x-1)) := by funext x; dsimp [M]; ring
    rw [he]
    exact hc.mul_right
end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
namespace Elasticity
variable {Ω : Set X} {l₁ m₁ l₂ m₂ : X → ℝ}

lemma energy_coeff_congr_ae
    (hl : l₁ =ᵐ[volume.restrict Ω] l₂) (hm : m₁ =ᵐ[volume.restrict Ω] m₂) :
    energy Ω l₁ m₁=energy Ω l₂ m₂ := by
  funext u v
  apply integral_congr_ae
  filter_upwards [hl,hm] with x hxl hxm
  rw [hxl,hxm]

/-- The variational DN definition really depends only on the interior
coefficients, including its choice branch. No exterior identification is presumed. -/
theorem DN_coeff_congr_ae
    (hl : l₁ =ᵐ[volume.restrict Ω] l₂) (hm : m₁ =ᵐ[volume.restrict Ω] m₂) :
    DN Ω l₁ m₁=DN Ω l₂ m₂ := by
  have he := energy_coeff_congr_ae hl hm
  have hws : WeakSolution Ω l₁ m₁=WeakSolution Ω l₂ m₂ := by
    funext u
    apply propext
    unfold WeakSolution
    rw [he]
  have hsol : dirichletSolution Ω l₁ m₁=dirichletSolution Ω l₂ m₂ := by
    funext f
    unfold dirichletSolution
    rw [hws]
  change (fun (f g : BoundaryData Ω) => energy Ω l₁ m₁ (dirichletSolution Ω l₁ m₁ f) g.out) =
    (fun (f g : BoundaryData Ω) => energy Ω l₂ m₂ (dirichletSolution Ω l₂ m₂ f) g.out)
  rw [he,hsol]

theorem DN_coeff_congr (hΩ : MeasurableSet Ω) (hl : EqOn l₁ l₂ Ω) (hm : EqOn m₁ m₂ Ω) :
    DN Ω l₁ m₁=DN Ω l₂ m₂ := by
  apply DN_coeff_congr_ae
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hl hx
  · filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hm hx
end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonExterior
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
attribute [local instance] Classical.propDecidable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma extension_jets {K : Set E} {f g : E → ℝ} (h : f =ᶠ[𝓝ˢ K] g)
    {x : E} (hx : x∈K) (n : ℕ) : iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x := by
  exact ((h.filter_mono (nhds_le_nhdsSet hx)).iteratedFDeriv ℝ n).self_of_nhds

/-- Once actual boundary jets have been determined, the source common exterior
reduction follows, including every bounded component of the exterior. -/
theorem common_exterior_of_all_jets {Ω U₁ U₂ : Set E} (hc : IsCompact (closure Ω))
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (h₁ : closure Ω⊆U₁) (h₂ : closure Ω⊆U₂)
    (l₁ m₁ l₂ m₂ : E → ℝ)
    (hl₁ : ContDiffOn ℝ (⊤ : ℕ∞) l₁ U₁) (hm₁ : ContDiffOn ℝ (⊤ : ℕ∞) m₁ U₁)
    (hl₂ : ContDiffOn ℝ (⊤ : ℕ∞) l₂ U₂) (hm₂ : ContDiffOn ℝ (⊤ : ℕ∞) m₂ U₂)
    (hp₁ : ∀ x∈closure Ω, 0 < m₁ x ∧ 0 < 3*l₁ x+2*m₁ x)
    (hp₂ : ∀ x∈closure Ω, 0 < m₂ x ∧ 0 < 3*l₂ x+2*m₂ x)
    (hjl : ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x)
    (hjm : ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) :
    ∃ L₁ M₁ L₂ M₂ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) L₁ ∧ ContDiff ℝ (⊤ : ℕ∞) M₁ ∧
      ContDiff ℝ (⊤ : ℕ∞) L₂ ∧ ContDiff ℝ (⊤ : ℕ∞) M₂ ∧
      EqOn L₁ l₁ Ω ∧ EqOn M₁ m₁ Ω ∧ EqOn L₂ l₂ Ω ∧ EqOn M₂ m₂ Ω ∧
      (∀ x, 0 < M₁ x ∧ 0 < 3*L₁ x+2*M₁ x) ∧
      (∀ x, 0 < M₂ x ∧ 0 < 3*L₂ x+2*M₂ x) ∧
      EqOn L₂ L₁ Ωᶜ ∧ EqOn M₂ M₁ Ωᶜ ∧
      ∃ K, IsCompact K ∧ ∀ x∉K, L₁ x=0 ∧ M₁ x=1 ∧ L₂ x=0 ∧ M₂ x=1 := by
  obtain ⟨L₁,M₁,hL₁,hM₁,heL₁,heM₁,hp,hcL,hcM⟩ :=
    admissible_global_extension hc hU₁ h₁ l₁ m₁ hl₁ hm₁ hp₁
  obtain ⟨F,hF,_,heF⟩ := smooth_global_extension hc hU₂ h₂ l₂ hl₂
  obtain ⟨G,hG,_,heG⟩ := smooth_global_extension hc hU₂ h₂ m₂ hm₂
  let L₂ := Ω.piecewise F L₁
  let M₂ := Ω.piecewise G M₁
  have hL₂ : ContDiff ℝ (⊤ : ℕ∞) L₂ := by
    apply smooth_piecewise_all_jets Ω F L₁ hF hL₁
    intro n x hx
    rw [extension_jets heF (frontier_subset_closure hx),extension_jets heL₁ (frontier_subset_closure hx)]
    exact hjl n x hx
  have hM₂ : ContDiff ℝ (⊤ : ℕ∞) M₂ := by
    apply smooth_piecewise_all_jets Ω G M₁ hG hM₁
    intro n x hx
    rw [extension_jets heG (frontier_subset_closure hx),extension_jets heM₁ (frontier_subset_closure hx)]
    exact hjm n x hx
  have heL₂ : EqOn L₂ l₂ Ω := by
    intro x hx
    exact (piecewise_eq_of_mem Ω F L₁ hx).trans (heF.self_of_nhdsSet (subset_closure hx))
  have heM₂ : EqOn M₂ m₂ Ω := by
    intro x hx
    exact (piecewise_eq_of_mem Ω G M₁ hx).trans (heG.self_of_nhdsSet (subset_closure hx))
  refine ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,
    fun x hx => heL₁.self_of_nhdsSet (subset_closure hx),
    fun x hx => heM₁.self_of_nhdsSet (subset_closure hx),heL₂,heM₂,hp,?_,?_,?_,?_,?_,?_⟩
  · intro x
    by_cases hx : x∈Ω
    · rw [heL₂ hx,heM₂ hx]
      exact hp₂ x (subset_closure hx)
    · simpa only [L₂,M₂,piecewise_eq_of_notMem Ω _ _ hx] using hp x
  · intro x hx
    exact piecewise_eq_of_notMem Ω F L₁ hx
  · intro x hx
    exact piecewise_eq_of_notMem Ω G M₁ hx
  · exact closure Ω ∪ tsupport L₁ ∪ tsupport (fun x => M₁ x-1)
  · exact (hc.union hcL).union hcM
  · intro x hx
    have hO : x∉Ω := fun hh => hx (Or.inl (Or.inl (subset_closure hh)))
    have hL : L₁ x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inl (Or.inr hh)))
    have hz : (fun x => M₁ x-1) x=0 := image_eq_zero_of_notMem_tsupport (f := fun y => M₁ y-1) (fun hh => hx (Or.inr hh))
    have hM : M₁ x=1 := sub_eq_zero.mp hz
    exact ⟨hL,hM,(piecewise_eq_of_notMem Ω F L₁ hO).trans hL,
      (piecewise_eq_of_notMem Ω G M₁ hO).trans hM⟩
end ElasticityBoundary

end
end
section
noncomputable section
open Set MeasureTheory
namespace Elasticity

lemma Admissible.common_neighborhood {Ω : Set X} {l m : X → ℝ} (h : Admissible Ω l m) :
    ∃ U : Set X,IsOpen U ∧ closure Ω⊆U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) l U ∧ ContDiffOn ℝ (⊤ : ℕ∞) m U := by
  obtain ⟨U,hU,hsub,hLu⟩ := h.1
  obtain ⟨V,hV,hsub',hMv⟩ := h.2.1
  exact ⟨U∩V,hU.inter hV,subset_inter hsub hsub',hLu.mono inter_subset_left,
    hMv.mono inter_subset_right⟩

lemma admissible_of_global {Ω : Set X} {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*l x+2*m x) : Admissible Ω l m :=
  ⟨⟨univ,isOpen_univ,subset_univ _,hl.contDiffOn⟩,
    ⟨univ,isOpen_univ,subset_univ _,hm.contDiffOn⟩,fun x _ => hp x⟩

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryJets
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Smooth-on-closure all-jet determination from the actual real physical DN
map, for every bounded connected domain with honest C-infinity boundary. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
variable {Ω : Set X}

theorem admissible_boundary_jets (hD : SourceDomain Ω) (l₁ m₁ l₂ m₂ : X → ℝ)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x) ∧
      (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) := by
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,hL₁,hM₁,heL₁,heM₁,hp₁,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₁ hs₁ l₁ m₁ hl₁ hm₁ ha₁.2.2
  obtain ⟨L₂,M₂,hL₂,hM₂,heL₂,heM₂,hp₂,_,_⟩ :=
    admissible_global_extension hD.2.2.1.isCompact_closure hU₂ hs₂ l₂ m₂ hl₂ hm₂ ha₂.2.2
  have hd : DN Ω L₁ M₁=DN Ω L₂ M₂ :=
    (DN_coeff_congr hD.1.measurableSet
      (fun x hx => heL₁.self_of_nhdsSet (subset_closure hx))
      (fun x hx => heM₁.self_of_nhdsSet (subset_closure hx))).trans
      (hDN.trans (DN_coeff_congr hD.1.measurableSet
        (fun x hx => heL₂.self_of_nhdsSet (subset_closure hx))
        (fun x hx => heM₂.self_of_nhdsSet (subset_closure hx))).symm)
  have h := boundary_jets_global hD.2.2.2 hD.1 hD.2.2.1 hL₁ hM₁ hL₂ hM₂
    (admissible_of_global hL₁ hM₁ hp₁) (admissible_of_global hL₂ hM₂ hp₂) hd
  have je {f g : X → ℝ} (he : f =ᶠ[𝓝ˢ (closure Ω)] g) (n : ℕ) (x : X) (hx : x∈frontier Ω) :
      iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x :=
    ((he.filter_mono (nhds_le_nhdsSet (frontier_subset_closure hx))).iteratedFDeriv ℝ n).eq_of_nhds
  constructor
  · intro n x hx
    simpa only [je heL₁ n x hx,je heL₂ n x hx] using h.1 n x hx
  · intro n x hx
    simpa only [je heM₁ n x hx,je heM₂ n x hx] using h.2 n x hx

end ElasticityBoundaryPacket

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity
/-- Full common-exterior reduction from the physical DN map. In particular no
prior boundary jets or agreement on a boundary neighbourhood is assumed. -/
theorem admissible_common_exterior {Ω : Set X} (hD : SourceDomain Ω)
    (l₁ m₁ l₂ m₂ : X → ℝ) (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∃ L₁ M₁ L₂ M₂ : X → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) L₁ ∧ ContDiff ℝ (⊤ : ℕ∞) M₁ ∧
      ContDiff ℝ (⊤ : ℕ∞) L₂ ∧ ContDiff ℝ (⊤ : ℕ∞) M₂ ∧
      EqOn L₁ l₁ Ω ∧ EqOn M₁ m₁ Ω ∧ EqOn L₂ l₂ Ω ∧ EqOn M₂ m₂ Ω ∧
      (∀ x,0 < M₁ x ∧ 0<3*L₁ x+2*M₁ x) ∧
      (∀ x,0 < M₂ x ∧ 0<3*L₂ x+2*M₂ x) ∧
      EqOn L₂ L₁ Ωᶜ ∧ EqOn M₂ M₁ Ωᶜ ∧
      DN Ω L₁ M₁=DN Ω L₂ M₂ ∧
      ∃ K,IsCompact K ∧ ∀ x∉K,L₁ x=0 ∧ M₁ x=1 ∧ L₂ x=0 ∧ M₂ x=1 := by
  obtain ⟨hjl,hjm⟩ := admissible_boundary_jets hD l₁ m₁ l₂ m₂ ha₁ ha₂ hDN
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,hK⟩ :=
    ElasticityBoundary.common_exterior_of_all_jets hD.2.2.1.isCompact_closure
      hU₁ hU₂ hs₁ hs₂ l₁ m₁ l₂ m₂ hl₁ hm₁ hl₂ hm₂ ha₁.2.2 ha₂.2.2 hjl hjm
  refine ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,?_,hK⟩
  exact (DN_coeff_congr hD.1.measurableSet heL₁ heM₁).trans
    (hDN.trans (DN_coeff_congr hD.1.measurableSet heL₂ heM₂).symm)
end ElasticityBoundaryPacket

end
end
section
noncomputable section
open Set
namespace Elasticity
open ElasticityAugmented ElasticityCoeffBounds

lemma exteriorConstant_of_eq_const {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set X} (hK : IsCompact K) (c : ℝ) (hc : ∀ x∉K,f x=c) :
    ExteriorConstant (smoothOfReal f hf) := by
  refine ⟨(c : ℂ),hK.of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra h
  apply hx
  change (f x : ℂ)-(c : ℂ)=0
  rw [hc x h,sub_self]

/-- Exact global smooth isotropic elasticity uniqueness on every bounded
connected domain with genuine smooth open boundary charts. Boundary jets,
common exterior, physical transfer, weak limits, constrained common frames,
parameter holomorphy and transport matching are all proved dependencies. -/
theorem source_global_uniqueness (Ω : Set X) (hD : SourceDomain Ω)
    (lam₁ mu₁ lam₂ mu₂ : X → ℝ)
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂) :
    (∀ x∈Ω,lam₁ x=lam₂ x) ∧ (∀ x∈Ω,mu₁ x=mu₂ x) := by
  obtain ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,hd,K,hK,hout⟩ :=
    ElasticityBoundaryPacket.admissible_common_exterior hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN
  let l : Fin 2 → X → ℝ := ![L₁,L₂]
  let m : Fin 2 → X → ℝ := ![M₁,M₂]
  have hl (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (l q) := by fin_cases q; exact hL₁; exact hL₂
  have hm (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (m q) := by fin_cases q; exact hM₁; exact hM₂
  have hp (q : Fin 2) (x : X) : 0 < m q x ∧ 0<3*l q x+2*m q x := by
    fin_cases q; exact hp₁ x; exact hp₂ x
  have hcll (q : Fin 2) : ExteriorConstant (smoothOfReal (l q) (hl q)) := by
    apply exteriorConstant_of_eq_const (hl q) hK 0
    intro x hx
    fin_cases q; exact (hout x hx).1; exact (hout x hx).2.2.1
  have hclm (q : Fin 2) : ExteriorConstant (smoothOfReal (m q) (hm q)) := by
    apply exteriorConstant_of_eq_const (hm q) hK 1
    intro x hx
    fin_cases q; exact (hout x hx).2.1; exact (hout x hx).2.2.2
  have he (x) (hx : x∉Ω) : l 0 x=l 1 x ∧ m 0 x=m 1 x := ⟨(hexL hx).symm,(hexM hx).symm⟩
  have hh := dn_global_coefficients_equal hD.1 hD.2.2.1 l m hl hm hp hcll hclm he hd
  constructor
  · intro x hx
    rw [← heL₁ hx,← heL₂ hx]
    exact congrFun hh.1 x
  · intro x hx
    rw [← heM₁ hx,← heM₂ hx]
    exact congrFun hh.2 x
end Elasticity

end
end
theorem Elasticity.global_uniqueness_oai : Elasticity.MainClaim := by
  intro Ω hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN
  exact Elasticity.source_global_uniqueness Ω hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN

end OAI
end

theorem solution : type_of% @OAI.Elasticity.global_uniqueness_oai := @OAI.Elasticity.global_uniqueness_oai
