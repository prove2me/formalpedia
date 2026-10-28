-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.profile_small_affine_grid_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:21:57.235355+00:00
-- url     : https://prove2.me/submissions/3ba61e12-f5ef-4fcc-9b68-3aebe6522338

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section
-- module Solutions.OAIQ4_Nl.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Integration
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma integrable_mul_compact_right {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left

lemma integral_mul_partial {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    (∫ x, f x * coordPartial g i x) = -(∫ x, coordPartial f i x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_compact_right (smooth_partial hf i) hg hc
  · exact integrable_mul_compact_right hf (smooth_partial hg i) (compact_partial hc i)
  · exact integrable_mul_compact_right hf hg hc
  · intro x _
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x _
    exact (hg.differentiable (by simp)).differentiableAt


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Energy
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_tsupport_subset (f : Plane → ℝ) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Carleman
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_neg {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => -f y) i x = -coordPartial f i x := by
  simpa only [neg_one_mul] using partial_const_mul hf (-1) i x

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

namespace SharpNodal
namespace Profiles
open Carleman

lemma laplacian_const (c : ℝ) (x : Plane) : euclideanLaplacian (fun _ => c) x=0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h : coordPartial (fun _ => c) i=(fun _ => 0) := funext (partial_const c i)
  rw [h, partial_const]

lemma laplacian_tsupport_subset (f : Plane → ℝ) :
    tsupport (euclideanLaplacian f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  rw [(laplacian_eventuallyEq he).eq_of_nhds]
  exact laplacian_const _ _

end Profiles
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileTests
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

namespace SharpNodal.Profiles
open Carleman

lemma upperSemicontinuousOn_add_real {Ω : Set Plane} {V : Plane → EReal}
    {f : Plane → ℝ} (hV : UpperSemicontinuousOn V Ω) (hf : ContinuousOn f Ω) :
    UpperSemicontinuousOn (fun x => V x+(f x:EReal)) Ω := by
  apply hV.add' (continuous_coe_real_ereal.comp_continuousOn hf).upperSemicontinuousOn
  intro x hx
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_radiusSquare (x₀ : Plane) : Smooth (radiusSquare x₀) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_centeredQuadratic (A : BilinearForm) (x₀ : Plane) :
    Smooth (centeredQuadratic A x₀) := by
  exact contDiff_const.mul ((contDiff_const.clm_apply (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const))

lemma hasFDerivAt_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : HasFDerivAt (centeredQuadratic A x₀) (A (x-x₀)) x := by
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hAt : HasFDerivAt (fun y => A (y-x₀)) A x := by
    convert! A.hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  convert! (hAt.clm_apply ht).const_mul (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, id_eq]
  rw [hA y (x-x₀)]
  ring

lemma fderiv_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A) (x₀ : Plane) :
    fderiv ℝ (centeredQuadratic A x₀) = fun x => A (x-x₀) :=
  funext fun x => (hasFDerivAt_centeredQuadratic hA x₀ x).fderiv

lemma partial_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (centeredQuadratic A x₀) i x=A (x-x₀) (EuclideanSpace.single i 1) := by
  rw [coordPartial, fderiv_centeredQuadratic hA]

lemma partial2_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (centeredQuadratic A x₀) i) j x=
      A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  rw [show coordPartial (centeredQuadratic A x₀) i =
    fun y => A (y-x₀) (EuclideanSpace.single i 1) from funext (partial_centeredQuadratic hA x₀ i)]
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hh : HasFDerivAt (fun y => A (y-x₀) (EuclideanSpace.single i 1))
      (A.flip (EuclideanSpace.single i 1)) x := by
    convert! (A.flip (EuclideanSpace.single i 1)).hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hh.fderiv, ContinuousLinearMap.flip_apply]

lemma laplacian_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : euclideanLaplacian (centeredQuadratic A x₀) x=
      ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp only [euclideanLaplacian, partial2_centeredQuadratic hA]

lemma symmetric_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    SymmetricForm (fderiv ℝ (fderiv ℝ f) x₀) := by
  intro x y
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))).eq x y

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

lemma smooth_secondTaylorPolynomial (f : Plane → ℝ) (x₀ : Plane) :
    Smooth (secondTaylorPolynomial f x₀) :=
  (contDiff_const.add (contDiff_const.clm_apply (contDiff_id.sub contDiff_const))).add
    (smooth_centeredQuadratic _ _)

lemma secondTaylorPolynomial_self (f : Plane → ℝ) (x₀ : Plane) :
    secondTaylorPolynomial f x₀ x₀=f x₀ := by
  simp [secondTaylorPolynomial, centeredQuadratic]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma partial_clm_shift (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (fun y => L (y-x₀)) i x=L (EuclideanSpace.single i 1) := by
  have hd : HasFDerivAt (fun y => L (y-x₀)) L x := by
    convert! L.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hd.fderiv]

lemma partial_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (quadraticAffine c L A x₀) i x=
      L (EuclideanSpace.single i 1)+A (x-x₀) (EuclideanSpace.single i 1) := by
  have hL : Smooth (fun y => L (y-x₀)) :=
    contDiff_const.clm_apply (contDiff_id.sub contDiff_const)
  unfold quadraticAffine
  rw [partial_add (contDiff_const.add hL)
    (smooth_centeredQuadratic A x₀), partial_add contDiff_const hL, partial_const,
    partial_clm_shift, partial_centeredQuadratic hA, zero_add]

lemma laplacian_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) :
    euclideanLaplacian (quadraticAffine c L A x₀) x=formTrace A := by
  unfold euclideanLaplacian formTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (quadraticAffine c L A x₀) i =
    fun y => L (EuclideanSpace.single i 1)+coordPartial (centeredQuadratic A x₀) i y by
      ext y; rw [partial_quadraticAffine hA, partial_centeredQuadratic hA]]
  rw [partial_add contDiff_const (smooth_partial (smooth_centeredQuadratic A x₀) i),
    partial_const, zero_add, partial2_centeredQuadratic hA]

lemma innerForm_apply (x y : Plane) : innerForm x y=inner ℝ x y := rfl

lemma symmetric_innerForm : SymmetricForm innerForm := by
  intro x y
  exact real_inner_comm y x

lemma formTrace_innerForm : formTrace innerForm=2 := by
  simp [formTrace, innerForm_apply]

lemma formTrace_smul (c : ℝ) (A : BilinearForm) : formTrace (c • A)=c*formTrace A := by
  simp only [formTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

lemma centeredQuadratic_inner_smul (δ : ℝ) (x₀ x : Plane) :
    centeredQuadratic ((2*δ) • innerForm) x₀ x=δ*‖x-x₀‖^2 := by
  simp only [centeredQuadratic, smul_apply, smul_eq_mul, innerForm_apply,
    real_inner_self_eq_norm_sq]
  ring

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileExtraction
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma upper_test_of_maximum {V : Plane → EReal} {q : Plane → ℝ} {F : Set Plane}
    {x₀ : Plane} (hx₀ : x₀∈interior F) (hfinite : V x₀≠⊤ ∧ V x₀≠⊥)
    (hmax : IsMaxOn (fun x => V x+((-q x:ℝ):EReal)) F x₀) :
    IsUpperTest V (fun x => q x+(V x₀).toReal-q x₀) x₀ := by
  have hv := EReal.coe_toReal hfinite.1 hfinite.2
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left, hv]
  · filter_upwards [mem_interior_iff_mem_nhds.mp hx₀] with x hx
    apply (EReal.addLECancellable_coe (-q x)).add_le_add_iff_right.mp
    have hh : V x+((-q x:ℝ):EReal) ≤ V x₀+((-q x₀:ℝ):EReal) := hmax hx
    rw [← hv, ← EReal.coe_add] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [← EReal.coe_add]
    congr 1
    ring

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subharmonic
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma full_test_local {Ω O : Set Plane} {V : Plane → EReal} {f : Plane → ℝ} {x₀ : Plane}
    (htest : FullTestProperty Ω V) (hO : IsOpen O) (hxO : x₀∈O) (hxΩ : x₀∈Ω)
    (hf : ContDiffOn ℝ ∞ f O) (ht : IsUpperTest V f x₀) :
    0≤euclideanLaplacian f x₀ := by
  obtain ⟨g,r,hg,hr,_,heq⟩ := smooth_extension_near hO hxO hf
  have hevent : g =ᶠ[𝓝 x₀] f := Filter.Eventually.mono (Metric.ball_mem_nhds x₀ hr) fun _ hx => heq _ hx
  have htg : IsUpperTest V g x₀ := by
    constructor
    · rw [hevent.eq_of_nhds]; exact ht.1
    · filter_upwards [ht.2,hevent] with x hx he
      rwa [he]
  have hh := htest g hg x₀ hxΩ htg
  rwa [(laplacian_eventuallyEq hevent).eq_of_nhds] at hh

lemma laplacian_add_local {O : Set Plane} {f g : Plane → ℝ} {x : Plane}
    (hO : IsOpen O) (hx : x∈O) (hf : ContDiffOn ℝ ∞ f O) (hg : Smooth g) :
    euclideanLaplacian (fun y => f y+g y) x=euclideanLaplacian f x+euclideanLaplacian g x := by
  obtain ⟨f',r,hf',hr,_,heq⟩ := smooth_extension_near hO hx hf
  have hevent : f'=ᶠ[𝓝 x] f := Filter.Eventually.mono (Metric.ball_mem_nhds x hr) fun _ hz => heq _ hz
  have hevent' : (fun y => f' y+g y)=ᶠ[𝓝 x] (fun y => f y+g y) := by
    filter_upwards [hevent] with y hy; rw [hy]
  rw [← (laplacian_eventuallyEq hevent').eq_of_nhds,laplacian_add hf' hg,
    (laplacian_eventuallyEq hevent).eq_of_nhds]

lemma laplacian_radiusSquare (x₀ x : Plane) : euclideanLaplacian (radiusSquare x₀) x=4 := by
  have heq : radiusSquare x₀=centeredQuadratic ((2:ℝ) • innerForm) x₀ := by
    ext y
    simpa only [radiusSquare,mul_one,one_mul] using (centeredQuadratic_inner_smul 1 x₀ y).symm
  have hs : SymmetricForm ((2:ℝ) • innerForm) := by
    intro y z
    simp only [smul_apply,smul_eq_mul,symmetric_innerForm y z]
  rw [heq,laplacian_centeredQuadratic hs]
  change formTrace ((2:ℝ) • innerForm)=4
  rw [formTrace_smul,formTrace_innerForm]
  norm_num

lemma laplacian_quadraticBarrier (a : Plane) (r ε m : ℝ) (x : Plane) :
    euclideanLaplacian (fun y => ε*(r^2-radiusSquare a y)+m) x= -4*ε := by
  have heq : (fun y => ε*(r^2-radiusSquare a y)+m)=
      (fun y => (ε*r^2+m)+(-ε)*radiusSquare a y) := by ext y; ring
  rw [heq,laplacian_add contDiff_const (contDiff_const.mul (smooth_radiusSquare a)),
    laplacian_const,laplacian_const_mul (smooth_radiusSquare a)]
  dsimp only
  rw [laplacian_radiusSquare]
  ring

theorem harmonic_comparison_of_full_test {Ω : Set Plane} {V : Plane → EReal}
    {h : Plane → ℝ} {a : Plane} {r : ℝ}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) (hr : 0 < r) (hball : Metric.closedBall a r⊆Ω)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball a r))
    (hc : ContinuousOn h (Metric.closedBall a r))
    (hΔ : ∀ x∈Metric.ball a r, euclideanLaplacian h x=0)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(h x:EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(h x:EReal) := by
  intro x hx
  by_contra hn
  have hgap : (0:EReal)<V x+((-h x:ℝ):EReal) := by
    have hhx := EReal.add_lt_add_right_coe (lt_of_not_ge hn) (-h x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhx
  obtain ⟨δ,hδ0,hδgap⟩ := EReal.lt_iff_exists_real_btwn.mp hgap
  have hδ : 0<δ := by exact_mod_cast hδ0
  let ε := δ/(r^2+1)
  have hε : 0<ε := div_pos hδ (by positivity)
  have hεmul : ε*(r^2+1)=δ := by dsimp [ε];field_simp
  let q : Plane → ℝ := fun y => h y+ε*(r^2-radiusSquare a y)
  have hbar : Smooth (fun y => ε*(r^2-radiusSquare a y)) :=
    contDiff_const.mul (contDiff_const.sub (smooth_radiusSquare a))
  have hq : ContinuousOn q (Metric.closedBall a r) := hc.add hbar.continuous.continuousOn
  have hqvalue : (0:EReal)<V x+((-q x:ℝ):EReal) := by
    have hle : ε*(r^2-radiusSquare a x)≤δ := by
      rw [← hεmul]
      apply mul_le_mul_of_nonneg_left _ hε.le
      have := sq_nonneg ‖x-a‖
      dsimp [radiusSquare]
      linarith
    have hhx := EReal.add_lt_add_right_coe hδgap (h x)
    have hlower : ((δ+h x:ℝ):EReal)<V x := by
      simpa only [← EReal.coe_add,add_assoc,neg_add_cancel,EReal.coe_zero,add_zero] using hhx
    have hqle : (q x:EReal)≤((δ+h x:ℝ):EReal) := by
      apply EReal.coe_le_coe_iff.mpr
      dsimp [q]; linarith
    have hhq := EReal.add_lt_add_right_coe (hqle.trans_lt hlower) (-q x)
    simpa only [← EReal.coe_add,add_neg_cancel,EReal.coe_zero] using hhq
  obtain ⟨y,hy,hmax⟩ := (upperSemicontinuousOn_add_real (hV.mono hball) hq.neg).exists_isMaxOn
    ⟨a,Metric.mem_closedBall_self hr.le⟩ (isCompact_closedBall a r)
  have hpos : (0:EReal)<V y+((-q y:ℝ):EReal) := hqvalue.trans_le (hmax hx)
  have hyint : y∈Metric.ball a r := by
    apply Metric.mem_ball.mpr
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hy)
    intro he
    have hybd : y∈Metric.sphere a r := Metric.mem_sphere.mpr he
    have hqbd : q y=h y := by
      have hdist : ‖y-a‖=r := by simpa only [Metric.mem_sphere,dist_eq_norm] using hybd
      simp only [q,radiusSquare,hdist,sub_self,mul_zero,add_zero]
    have hb := add_le_add (hbdry y hybd) (le_refl ((-q y:ℝ):EReal))
    rw [hqbd,← EReal.coe_add,add_neg_cancel,EReal.coe_zero] at hb
    apply (not_le_of_gt hpos)
    simpa only [hqbd] using hb
  have hfinite : V y≠⊤ ∧ V y≠⊥ := by
    refine ⟨htop y (hball hy),?_⟩
    intro he
    rw [he,EReal.bot_add] at hpos
    exact (not_lt_of_ge bot_le) hpos
  let m := (V y).toReal-q y
  have ht := upper_test_of_maximum (Metric.ball_subset_interior_closedBall hyint) hfinite hmax
  have ht' : IsUpperTest V (fun z => h z+(ε*(r^2-radiusSquare a z)+m)) y := by
    convert! ht using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    dsimp [q,m]
    ring
  have hs := full_test_local htest Metric.isOpen_ball hyint (hball hy)
    (hh.add (hbar.add contDiff_const).contDiffOn) ht'
  rw [laplacian_add_local Metric.isOpen_ball hyint hh (hbar.add contDiff_const),
    hΔ y hyint,laplacian_quadraticBarrier,zero_add] at hs
  linarith
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma plane_laplacian_eq_mathlib {f : Plane → ℝ} (hf : Smooth f) :
    euclideanLaplacian f = Δ f := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  exact (hessian_on_basis hf x i i).symm

lemma laplacian_comp_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ (f∘e) = (Δ f)∘e := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f∘e) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  have hh := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
    hf x (i:=2) (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))
  rw [show (f∘e)=(f∘e.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  ext k
  fin_cases k <;> rfl

lemma plane_laplacian_comp_complex {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (x : Plane) :
    euclideanLaplacian (f∘planeComplex) x = (Δ f) (planeComplex x) := by
  have hf' : Smooth (f∘planeComplex) := by
    convert! hf.comp planeComplex.toContinuousLinearEquiv.contDiff using 1
    all_goals try with_reducible_and_instances rfl
  rw [plane_laplacian_eq_mathlib hf', laplacian_comp_isometry planeComplex hf]
  rfl

lemma compare_complex_harmonic {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀ x∈Ω, V x≠⊤)
    (htest : FullTestProperty Ω V) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hΔ : ∀ z, (Δ f) z=0) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω)
    (hbdry : ∀ x∈Metric.sphere a r, V x≤(f (planeComplex x):EReal)) :
    ∀ x∈Metric.closedBall a r, V x≤(f (planeComplex x):EReal) := by
  apply harmonic_comparison_of_full_test hV htop htest hr hball
    (hf.comp planeComplex.toContinuousLinearEquiv.contDiff).contDiffOn
    (hf.continuous.comp planeComplex.continuous).continuousOn _ hbdry
  intro x _
  exact (plane_laplacian_comp_complex hf x).trans (hΔ _)
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma harmonic_extension_fourier_span {c : ℂ} {r : ℝ} (hr : r ≠ 0)
    {f : C(AddCircle (1:ℝ),ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
    ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=f t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n,rfl⟩ := hf
      have hbase (n : ℕ) : ∃ P : ℂ → ℂ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
          ∀ t : AddCircle (1:ℝ), P (c+(r:ℂ)*AddCircle.toCircle t)=fourier (n:ℤ) t := by
        refine ⟨fun z => ((z-c)/(r:ℂ))^n, ?_, ?_, ?_⟩
        · fun_prop
        · intro z _
          apply AnalyticAt.harmonicAt
          fun_prop
        · intro t
          simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr),
            fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]
      cases n with
      | ofNat n => exact hbase n
      | negSucc n =>
          obtain ⟨P,hP,hH,hf⟩ := hbase (n+1)
          refine ⟨fun z => conj (P z), ?_, ?_, ?_⟩
          · exact Complex.conjCLE.contDiff.comp hP
          · exact hH.comp_CLM Complex.conjCLE.toContinuousLinearMap
          · intro t
            change conj (P _) = fourier (-(↑(n+1):ℤ)) t
            rw [hf,fourier_neg]
  | zero =>
      exact ⟨0,contDiff_const,fun _ _ => harmonicAt_const 0,fun _ => rfl⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨P,hP,hH,hf⟩ := ihf
      obtain ⟨Q,hQ,hJ,hg⟩ := ihg
      exact ⟨P+Q,hP.add hQ,hH.add hJ,fun t => by simpa only [Pi.add_apply,ContinuousMap.add_apply] using congrArg₂ (·+·) (hf t) (hg t)⟩
  | smul a f hf ih =>
      obtain ⟨P,hP,hH,hf⟩ := ih
      exact ⟨a • P,hP.const_smul a,hH.comp_CLM (ContinuousLinearMap.mul ℝ ℂ a),fun t => by simpa only [Pi.smul_apply,ContinuousMap.smul_apply] using congrArg (a • ·) (hf t)⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma exists_circle_param {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z∈Metric.sphere c r) :
    ∃ t : AddCircle (1:ℝ), z=c+(r:ℂ)*AddCircle.toCircle t := by
  have hnorm : ‖(z-c)/(r:ℂ)‖=1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    rw [← dist_eq_norm,Metric.mem_sphere.mp hz,div_self hr.ne']
  let w : Circle := ⟨(z-c)/(r:ℂ),mem_sphere_zero_iff_norm.mpr hnorm⟩
  obtain ⟨t,ht⟩ := (AddCircle.homeomorphCircle (T:=(1:ℝ)) one_ne_zero).surjective w
  refine ⟨t,?_⟩
  have ht' : (AddCircle.toCircle t : ℂ)=(z-c)/(r:ℂ) := by
    simpa only [AddCircle.homeomorphCircle_apply] using congrArg (fun z : Circle => (z:ℂ)) ht
  rw [ht',mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  exact (add_sub_cancel c z).symm

lemma approximate_circle_by_harmonic {c : ℂ} {r ε : ℝ} (hr : 0 < r) (hε : 0<ε)
    {g : ℂ → ℝ} (hg : Continuous g) :
    ∃ P : ℂ → ℝ, ContDiff ℝ ∞ P ∧ HarmonicOnNhd P univ ∧
      ∀ z∈Metric.sphere c r, |P z-g z|<ε := by
  let f : C(AddCircle (1:ℝ),ℂ) := ⟨fun t => (g (c+(r:ℂ)*AddCircle.toCircle t):ℂ),by fun_prop⟩
  have hcl : f ∈ closure (Submodule.span ℂ (Set.range (@fourier (1:ℝ))) : Set C(AddCircle (1:ℝ),ℂ)) := by
    change f ∈ (Submodule.span ℂ (Set.range (@fourier (1:ℝ)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨q,hq,hfq⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨P,hP,hH,hbdry⟩ := harmonic_extension_fourier_span (c:=c) hr.ne' hq
  refine ⟨fun z => (P z).re, Complex.reCLM.contDiff.comp hP,hH.comp_CLM Complex.reCLM,?_⟩
  intro z hz
  obtain ⟨t,rfl⟩ := exists_circle_param hr hz
  change |(P (c+(r:ℂ)*AddCircle.toCircle t)).re-g (c+(r:ℂ)*AddCircle.toCircle t)|<ε
  rw [hbdry]
  have hqt := (ContinuousMap.dist_apply_le_dist (f:=f) (g:=q) t).trans_lt hfq
  have h := (Complex.abs_re_le_norm (q t-f t)).trans_lt (by
    simpa only [dist_eq_norm,norm_sub_rev] using hqt)
  simpa only [Complex.sub_re,ContinuousMap.coe_mk, f,Complex.ofReal_re] using h

theorem submean_continuous_majorant {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (htop : ∀x∈Ω,V x≠⊤)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hbdry : ∀ x∈Metric.sphere a r,V x≤(g (planeComplex x):EReal)) :
    V a≤((Real.circleAverage g (planeComplex a) r:ℝ):EReal) := by
  have ha : a∈Metric.closedBall a r := Metric.mem_closedBall_self hr.le
  by_cases hbot : V a=⊥
  · simp [hbot]
  have hcoe := EReal.coe_toReal (htop a (hball ha)) hbot
  rw [← hcoe,EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P,hP,hH,happrox⟩ := approximate_circle_by_harmonic (c:=planeComplex a) hr (half_pos hε) hg
  let H : ℂ → ℝ := fun z => P z+ε/2
  have hHs : ContDiff ℝ ∞ H := hP.add contDiff_const
  have hHh : HarmonicOnNhd H univ := hH.add (fun _ _ => harmonicAt_const (ε/2))
  have hle : V a≤(H (planeComplex a):EReal) := by
    apply compare_complex_harmonic hV htop htest hHs (fun z => (hHh z (mem_univ _)).2.self_of_nhds) hr hball _ a ha
    intro x hx
    have hx' : planeComplex x∈Metric.sphere (planeComplex a) r := by
      simpa only [Metric.mem_sphere,planeComplex.isometry.dist_eq] using hx
    apply (hbdry x hx).trans
    apply EReal.coe_le_coe_iff.mpr
    exact le_of_lt (by have := (abs_lt.mp (happrox _ hx')).1; dsimp [H]; linarith)
  have hmean : H (planeComplex a)≤Real.circleAverage g (planeComplex a) r+ε := by
    rw [← hHh.mono (subset_univ _) |>.circleAverage_eq]
    have hcomp := Real.circleAverage_mono (c:=planeComplex a) (R:=r) hHs.continuous.continuousOn.circleIntegrable'
      (hg.add continuous_const).continuousOn.circleIntegrable' (f₂:=fun z => g z+ε) ?_
    · simpa only [show (fun z => g z+ε)=g+(fun _ => ε) from rfl,
        Real.circleAverage_add hg.continuousOn.circleIntegrable' continuous_const.continuousOn.circleIntegrable',
        Real.circleAverage_const] using hcomp
    · intro z hz
      have := (abs_lt.mp (happrox z (by simpa [abs_of_pos hr] using hz))).2
      dsimp [H]
      linarith
  exact (EReal.coe_le_coe_iff.mp (hcoe ▸ hle)).trans hmean
end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Regularization
attribute [-instance] _root_.OAI.SharpNodal.Profiles.circleParameter_isProbability _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

variable {X : Type*} [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma coe_truncBelow {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    (truncBelow V n x:EReal)=max (V x) ((-(n:ℝ):ℝ):EReal) := by
  apply EReal.coe_toReal
  · apply ne_of_lt
    exact max_lt (hx.trans_lt (by simp)) (EReal.coe_lt_top _)
  · exact ne_of_gt ((EReal.bot_lt_coe (-(n:ℝ))).trans_le (le_max_right _ _))

omit [PseudoMetricSpace X] in
lemma truncBelow_nonpos {V : X → EReal} {n : ℕ} {x : X} (hx : V x≤0) :
    truncBelow V n x≤0 := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx]
  exact max_le hx (by exact_mod_cast (neg_nonpos.mpr (Nat.cast_nonneg n):-(n:ℝ)≤0))

omit [PseudoMetricSpace X] in
lemma truncBelow_antitone {V : X → EReal} {x : X} (hx : V x≤0) :
    Antitone (fun n => truncBelow V n x) := by
  intro m n hmn
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncBelow hx,coe_truncBelow hx]
  exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hmn)))

lemma regularize_bdd {K : Set X} {V : X → EReal} (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) :
    BddAbove (Set.range fun y : K => truncBelow V n y-(n:ℝ)*dist x y) := by
  refine ⟨0,?_⟩
  rintro _ ⟨y,rfl⟩
  exact sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans (mul_nonneg (Nat.cast_nonneg n) dist_nonneg))

lemma supRegularize_nonpos {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) (x : X) : supRegularize K V n x≤0 := by
  let : Nonempty K := hK.to_subtype
  exact ciSup_le (fun y => sub_nonpos.mpr ((truncBelow_nonpos (hV y y.2)).trans
    (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)))

lemma supRegularize_majorant {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) (n : ℕ) {x : X} (hx : x∈K) : V x≤(supRegularize K V n x:EReal) := by
  apply (le_max_left (V x) ((-(n:ℝ):ℝ):EReal)).trans
  rw [← coe_truncBelow (hV x hx)]
  apply EReal.coe_le_coe_iff.mpr
  have := le_ciSup (regularize_bdd hV n x) (⟨x,hx⟩:K)
  simpa only [supRegularize,Subtype.coe_mk,dist_self,mul_zero,sub_zero] using this

lemma supRegularize_antitone {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (x : X) : Antitone (fun n => supRegularize K V n x) := by
  let : Nonempty K := hK.to_subtype
  intro m n hmn
  apply ciSup_le
  intro y
  apply le_trans _ (le_ciSup (regularize_bdd hV m x) y)
  exact sub_le_sub (truncBelow_antitone (hV y y.2) hmn)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) dist_nonneg)

lemma supRegularize_lipschitz {K : Set X} {V : X → EReal} (hK : K.Nonempty)
    (hV : ∀x∈K,V x≤0) (n : ℕ) : LipschitzWith (n:ℝ≥0) (supRegularize K V n) := by
  let : Nonempty K := hK.to_subtype
  have hdiff (x y : X) : supRegularize K V n x≤ supRegularize K V n y+(n:ℝ)*dist x y := by
    apply ciSup_le
    intro z
    have hle := le_ciSup (regularize_bdd hV n y) z
    change truncBelow V n z-(n:ℝ)*dist y z≤ supRegularize K V n y at hle
    have hd := dist_triangle_right y z x
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hd hn
    simp only [dist_comm y x,dist_comm (z:X) x] at hm
    linarith
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq,abs_le]
  have hxy := hdiff x y
  have hyx := hdiff y x
  simp only [dist_comm y x,NNReal.coe_natCast] at hyx ⊢
  constructor <;> linarith

lemma supRegularize_eventually_below {K : Set X} {V : X → EReal}
    (hV : ∀ x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) {a : ℝ} (ha : V x<(a:EReal)) :
    ∃ n : ℕ, supRegularize K V n x≤a := by
  let : Nonempty K := ⟨⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhdsWithin_iff.mp (husc a ha)
  obtain ⟨n,hn⟩ := exists_nat_gt (max (-a) (-a/δ))
  have hna : -(n:ℝ)≤a := by have := (le_max_left (-a) (-a/δ)).trans_lt hn; linarith
  have hnδ : -a<(n:ℝ)*δ := (div_lt_iff₀ hδ).mp ((le_max_right (-a) (-a/δ)).trans_lt hn)
  refine ⟨n,?_⟩
  apply ciSup_le
  intro y
  by_cases hd : dist x y<δ
  · have hy : V y<(a:EReal) := hnear ⟨by simpa only [Metric.mem_ball,dist_comm] using hd,y.2⟩
    have htr : truncBelow V n y≤a := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncBelow (hV y y.2)]
      exact max_le hy.le (EReal.coe_le_coe_iff.mpr hna)
    exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg n) dist_nonneg)).trans htr
  · have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hd) (Nat.cast_nonneg n : 0≤(n:ℝ))
    have ht := truncBelow_nonpos (n:=n) (hV y y.2)
    linarith

lemma iInf_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    (⨅ n : ℕ, (supRegularize K V n x:EReal))=V x := by
  apply le_antisymm
  · by_contra h
    obtain ⟨a,ha,ha'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
    obtain ⟨n,hn⟩ := supRegularize_eventually_below hV hx husc ha
    exact (not_le_of_gt ha') ((iInf_le (fun n => (supRegularize K V n x:EReal)) n).trans (EReal.coe_le_coe_iff.mpr hn))
  · exact le_iInf (fun n => supRegularize_majorant hV n hx)

lemma tendsto_supRegularize {K : Set X} {V : X → EReal}
    (hV : ∀x∈K,V x≤0) {x : X} (hx : x∈K)
    (husc : UpperSemicontinuousWithinAt V K x) :
    Tendsto (fun n => (supRegularize K V n x:EReal)) atTop (𝓝 (V x)) := by
  rw [← iInf_supRegularize hV hx husc]
  exact tendsto_atTop_iInf (EReal.coe_strictMono.monotone.comp_antitone
    (supRegularize_antitone ⟨x,hx⟩ hV x))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleAverage_eq_integral_parameter (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r=∫ t, f (circleMap c r t) ∂circleParameterMeasure := by
  rw [circleParameterMeasure,integral_smul_measure,Real.circleAverage,
    intervalIntegral.integral_of_le (by positivity)]
  simp only [ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]

lemma circleParameter_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f circleParameterMeasure := by
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : 0≤2*Real.pi)).mp
    (hf.intervalIntegrable 0 (2*Real.pi))).smul_measure ENNReal.ofReal_ne_top

lemma toENNReal_coe_real (x : ℝ) : (x:EReal).toENNReal=ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x),EReal.toReal_coe]

theorem circle_submean {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω) :
    (∫⁻ t, (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal
      ∂circleParameterMeasure) ≤ (-V a).toENNReal := by
  let K := Metric.sphere a r
  have hK : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKΩ : K⊆Ω := Metric.sphere_subset_closedBall.trans hball
  have hnegK : ∀ x∈K,V x≤0 := fun x hx => hneg x (hKΩ hx)
  let g : ℕ → ℂ → ℝ := fun n z => supRegularize K V n (planeComplex.symm z)
  have hg (n : ℕ) : Continuous (g n) :=
    (supRegularize_lipschitz hK hnegK n).continuous.comp planeComplex.symm.continuous
  let p : ℝ → Plane := fun t => planeComplex.symm (circleMap (planeComplex a) r t)
  have hpK (t : ℝ) : p t∈K := by
    change dist (planeComplex.symm (circleMap (planeComplex a) r t)) a=r
    rw [← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    simpa only [planeComplex.apply_symm_apply] using Metric.mem_sphere.mp (circleMap_mem_sphere (planeComplex a) hr.le t)
  have hlim (t : ℝ) : Tendsto (fun n => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t)))
      atTop (𝓝 ((-V (p t)).toENNReal)) := by
    have h := (tendsto_supRegularize hnegK (hpK t)
      ((hV _ (hKΩ (hpK t))).mono hKΩ)).neg
    have h' := EReal.continuous_toENNReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def,← EReal.coe_neg,toENNReal_coe_real,g,p] using h'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t))
  have hf (n : ℕ) : Measurable (f n) := by
    exact ENNReal.continuous_ofReal.measurable.comp ((hg n).comp (continuous_circleMap _ _)).neg.measurable
  have hmono : Monotone f := by
    intro m n hmn t
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (supRegularize_antitone hK hnegK (p t) hmn))
  have hiSup (t : ℝ) : (⨆ n,f n t)=(-V (p t)).toENNReal :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun m n hmn => hmono hmn t)) (hlim t)
  change (∫⁻ t,(-V (p t)).toENNReal ∂circleParameterMeasure)≤_
  simp_rw [← hiSup]
  rw [lintegral_iSup hf hmono]
  apply iSup_le
  intro n
  have hfn : Continuous (fun t => -g n (circleMap (planeComplex a) r t)) :=
    ((hg n).comp (continuous_circleMap _ _)).neg
  have hfnpos : ∀t,0≤ -g n (circleMap (planeComplex a) r t) :=
    fun t => neg_nonneg.mpr (supRegularize_nonpos hK hnegK n (p t))
  rw [← ofReal_integral_eq_lintegral_ofReal (circleParameter_integrable hfn) (Filter.Eventually.of_forall hfnpos)]
  rw [integral_neg,← circleAverage_eq_integral_parameter]
  rw [← toENNReal_coe_real, EReal.coe_neg]
  apply EReal.toENNReal_le_toENNReal
  apply EReal.neg_le_neg_iff.mpr
  apply submean_continuous_majorant hV (fun x hx => ne_of_lt ((hneg x hx).trans_lt (by simp))) htest hr hball (hg n)
  intro x hx
  simpa only [g,planeComplex.symm_apply_apply] using supRegularize_majorant hnegK n hx
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleAverage_eq_integral_polar (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r=∫ t, f (circleMap c r t) ∂polarParameterMeasure := by
  have heq := ((periodic_circleMap c r).comp f).intervalIntegral_add_eq 0 (-Real.pi)
  simp only [Function.comp_def,zero_add, show -Real.pi+2*Real.pi=Real.pi by ring] at heq
  rw [polarParameterMeasure,integral_smul_measure,Real.circleAverage,heq,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),integral_Ioc_eq_integral_Ioo]
  simp only [ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]

lemma polarParameter_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f polarParameterMeasure := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [restrict_Ioo_eq_restrict_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)).mp
    (hf.intervalIntegrable (-Real.pi) Real.pi)

theorem circle_submean_polar {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r⊆Ω) :
    (∫⁻ t, (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal
      ∂polarParameterMeasure) ≤ (-V a).toENNReal := by
  let K := Metric.sphere a r
  have hK : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKΩ : K⊆Ω := Metric.sphere_subset_closedBall.trans hball
  have hnegK : ∀ x∈K,V x≤0 := fun x hx => hneg x (hKΩ hx)
  let g : ℕ → ℂ → ℝ := fun n z => supRegularize K V n (planeComplex.symm z)
  have hg (n : ℕ) : Continuous (g n) :=
    (supRegularize_lipschitz hK hnegK n).continuous.comp planeComplex.symm.continuous
  let p : ℝ → Plane := fun t => planeComplex.symm (circleMap (planeComplex a) r t)
  have hpK (t : ℝ) : p t∈K := by
    change dist (planeComplex.symm (circleMap (planeComplex a) r t)) a=r
    rw [← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    simpa only [planeComplex.apply_symm_apply] using Metric.mem_sphere.mp (circleMap_mem_sphere (planeComplex a) hr.le t)
  have hlim (t : ℝ) : Tendsto (fun n => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t)))
      atTop (𝓝 ((-V (p t)).toENNReal)) := by
    have h := (tendsto_supRegularize hnegK (hpK t)
      ((hV _ (hKΩ (hpK t))).mono hKΩ)).neg
    have h' := EReal.continuous_toENNReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def,← EReal.coe_neg,toENNReal_coe_real,g,p] using h'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (-g n (circleMap (planeComplex a) r t))
  have hf (n : ℕ) : Measurable (f n) := by
    exact ENNReal.continuous_ofReal.measurable.comp ((hg n).comp (continuous_circleMap _ _)).neg.measurable
  have hmono : Monotone f := by
    intro m n hmn t
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (supRegularize_antitone hK hnegK (p t) hmn))
  have hiSup (t : ℝ) : (⨆ n,f n t)=(-V (p t)).toENNReal :=
    tendsto_nhds_unique (tendsto_atTop_iSup (fun m n hmn => hmono hmn t)) (hlim t)
  change (∫⁻ t,(-V (p t)).toENNReal ∂polarParameterMeasure)≤_
  simp_rw [← hiSup]
  rw [lintegral_iSup hf hmono]
  apply iSup_le
  intro n
  have hfn : Continuous (fun t => -g n (circleMap (planeComplex a) r t)) :=
    ((hg n).comp (continuous_circleMap _ _)).neg
  have hfnpos : ∀t,0≤ -g n (circleMap (planeComplex a) r t) :=
    fun t => neg_nonneg.mpr (supRegularize_nonpos hK hnegK n (p t))
  rw [← ofReal_integral_eq_lintegral_ofReal (polarParameter_integrable hfn) (Filter.Eventually.of_forall hfnpos)]
  rw [integral_neg,← circleAverage_eq_integral_polar]
  rw [← toENNReal_coe_real, EReal.coe_neg]
  apply EReal.toENNReal_le_toENNReal
  apply EReal.neg_le_neg_iff.mpr
  apply submean_continuous_majorant hV (fun x hx => ne_of_lt ((hneg x hx).trans_lt (by simp))) htest hr hball (hg n)
  intro x hx
  simpa only [g,planeComplex.symm_apply_apply] using supRegularize_majorant hnegK n hx
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Set MeasureTheory Filter
namespace SharpNodal.Profiles
open Carleman

lemma polarCoord_eq_circleMap (r t : ℝ) : Complex.polarCoord.symm (r,t)=circleMap 0 r t := by
  simp only [Complex.polarCoord_symm_apply,circleMap,zero_add]
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_cos,Complex.ofReal_sin]

lemma lintegral_radius {R : ℝ} (hR : 0≤R) :
    (∫⁻ r in Ioo 0 R, ENNReal.ofReal r)=ENNReal.ofReal (R^2/2) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo 0 R) := by
    rw [IntegrableOn,restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp (continuous_id.intervalIntegrable 0 R)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,integral_id]
    simp only [zero_pow (by decide : (2:ℕ)≠0),sub_zero]
  · exact ae_restrict_of_forall_mem measurableSet_Ioo (fun _ hr => hr.1.le)

lemma lintegral_ball_le_of_angular {f : ℂ → ℝ≥0∞} {R : ℝ} (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap 0 r t))≤C) :
    (∫⁻ z in Metric.ball (0:ℂ) R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  by_cases hC : C=⊤
  · simp [hC,ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0<R^2/2)]
  let g := (Metric.ball (0:ℂ) R).indicator f
  rw [← lintegral_indicator measurableSet_ball,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1*g (Complex.polarCoord.symm p))≤_
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  apply (lintegral_prod_le _).trans
  calc
    (∫⁻ r in Ioi (0:ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r*g (Complex.polarCoord.symm (r,t)))
      ≤ ∫⁻ r in Ioi (0:ℝ), (Iio R).indicator (fun r => ENNReal.ofReal r*C) r := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases hrR : r<R
        · rw [indicator_of_mem (show r∈Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=f (circleMap 0 r t) := by
            dsimp [g]
            rw [indicator_of_mem,polarCoord_eq_circleMap]
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0 < r from hr)] using hrR
          simp_rw [heq]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul' le_rfl (hcircle r ⟨hr,hrR⟩)
        · rw [indicator_of_notMem (show r∉Iio R from hrR)]
          have heq (t : ℝ) : g (Complex.polarCoord.symm (r,t))=0 := by
            apply indicator_of_notMem
            simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos (show 0 < r from hr)] using hrR
          simp only [heq,mul_zero,lintegral_zero,le_refl]
    _ = ∫⁻ r in Ioo 0 R, ENNReal.ofReal r*C := by
      have hset : Iio R∩Ioi (0:ℝ)=Ioo 0 R := by
        ext r
        exact and_comm
      rw [setLIntegral_indicator measurableSet_Iio,hset]
    _ = ENNReal.ofReal (R^2/2)*C := by
      rw [lintegral_mul_const' _ _ hC,lintegral_radius hR.le]

lemma lintegral_ball_center_le_of_angular {f : ℂ → ℝ≥0∞} {c : ℂ} {R : ℝ}
    (hR : 0<R) {C : ℝ≥0∞}
    (hcircle : ∀ r∈Ioo 0 R, (∫⁻ t in Ioo (-Real.pi) Real.pi,f (circleMap c r t))≤C) :
    (∫⁻ z in Metric.ball c R,f z)≤ENNReal.ofReal (R^2/2)*C := by
  have heq : (∫⁻ z in Metric.ball c R,f z)=(∫⁻ z in Metric.ball (0:ℂ) R,f (c+z)) := by
    rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self _ c]
    apply lintegral_congr
    intro z
    by_cases hz : z∈Metric.ball (0:ℂ) R
    · rw [indicator_of_mem hz,indicator_of_mem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
    · rw [indicator_of_notMem hz,indicator_of_notMem]
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  rw [heq]
  apply lintegral_ball_le_of_angular hR
  intro r hr
  simpa only [circleMap,zero_add] using hcircle r hr
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma lintegral_plane_ball_complex (f : Plane → ℝ≥0∞) (a : Plane) (r : ℝ) :
    (∫⁻x in Metric.ball a r,f x)=
      ∫⁻z in Metric.ball (planeComplex a) r,f (planeComplex.symm z) := by
  rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball,
    ← planeComplex.symm.measurePreserving.lintegral_comp_emb planeComplex.symm.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro z
  have heq : planeComplex.symm z∈Metric.ball a r ↔ z∈Metric.ball (planeComplex a) r := by
    simp only [Metric.mem_ball,← planeComplex.isometry.dist_eq,planeComplex.apply_symm_apply]
  by_cases hz : z∈Metric.ball (planeComplex a) r
  · rw [indicator_of_mem hz,indicator_of_mem (heq.mpr hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (heq.not.mpr hz)]
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem disk_submean {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤
      ENNReal.ofReal (Real.pi*R^2)*(-V a).toENNReal := by
  rw [lintegral_plane_ball_complex]
  have hc : ∀ r∈Ioo 0 R,
      (∫⁻ t in Ioo (-Real.pi) Real.pi,
        (-V (planeComplex.symm (circleMap (planeComplex a) r t))).toENNReal)
      ≤ ENNReal.ofReal (2*Real.pi)*(-V a).toENNReal := by
    intro r hr
    have hbr : Metric.closedBall a r⊆Ω := by
      apply Subset.trans _ hball
      intro x hx
      exact lt_of_le_of_lt hx hr.2
    have hs := circle_submean_polar hV hneg htest hr.1 hbr
    rw [polarParameterMeasure,lintegral_smul_measure] at hs
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (2*Real.pi))) hs
    simpa only [smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤2*Real.pi),
      mul_inv_cancel₀ (by positivity : 2*Real.pi≠0),ENNReal.ofReal_one,one_mul] using hh
  apply (lintegral_ball_center_le_of_angular hR hc).trans_eq
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤R^2/2)]
  congr 2
  ring

theorem disk_lintegral_le_of_anchor {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) {a : Plane} {R C : ℝ} (hR : 0<R)
    (hball : Metric.ball a R⊆Ω) (hanchor : (-(C:ℝ):EReal)≤V a) :
    (∫⁻ x in Metric.ball a R, (-V x).toENNReal) ≤ ENNReal.ofReal (Real.pi*R^2)*ENNReal.ofReal C := by
  apply (disk_submean hV hneg htest hR hball).trans
  apply mul_le_mul' le_rfl
  rw [← toENNReal_coe_real]
  apply EReal.toENNReal_le_toENNReal
  simpa only [← EReal.coe_neg,neg_neg] using EReal.neg_le_neg_iff.mpr hanchor

theorem profile_lintegral_D8 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    {a : Plane} (ha : a∈Metric.closedBall 0 1) (hanchor : (-1:EReal)≤V a) :
    (∫⁻x in Metric.ball (0:Plane) 8,(-V x).toENNReal)≤ ENNReal.ofReal (100*Real.pi) := by
  have hsubset : Metric.ball (0:Plane) 8⊆Metric.ball a 10 := by
    intro x hx
    have hd := dist_triangle x 0 a
    have ha' : dist (0:Plane) a≤1 := by simpa only [dist_comm] using Metric.mem_closedBall.mp ha
    change dist x a<10
    change dist x 0<8 at hx
    linarith
  have hball : Metric.ball a 10⊆Metric.ball (0:Plane) 1000 := by
    intro x hx
    have hd := dist_triangle x a 0
    change dist a 0≤1 at ha
    change dist x a<10 at hx
    change dist x 0<1000
    linarith
  apply (lintegral_mono' (Measure.restrict_mono hsubset (le_refl volume)) (le_refl (fun x => (-V x).toENNReal))).trans
  have hh := disk_lintegral_le_of_anchor hV hneg htest (by norm_num : (0:ℝ)<10) hball (C:=1) (by simpa using hanchor)
  simpa only [show Real.pi*(10:ℝ)^2=100*Real.pi by ring,ENNReal.ofReal_one,mul_one] using hh
end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma usc_neg_toENNReal_aemeasurable {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) :
    AEMeasurable (fun x => (-V x).toENNReal) (volume.restrict Ω) := by
  apply aemeasurable_restrict_of_measurable_subtype hΩ
  exact EReal.continuous_toENNReal.measurable.comp
    (upperSemicontinuousOn_iff_restrict.mpr hV).measurable.neg

lemma profile_integrable_of_lintegral_ne_top {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (hfin : (∫⁻ x in Ω, (-V x).toENNReal)≠⊤) :
    IntegrableOn (fun x => (V x).toReal) Ω ∧ (∀ᵐx ∂volume.restrict Ω,V x≠⊥) := by
  have hm := usc_neg_toENNReal_aemeasurable hΩ hV
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin
  have heq : (fun x => (V x).toReal)=ᵐ[volume.restrict Ω]
      (fun x => -((-V x).toENNReal.toReal)) := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x hx)),
      EReal.toReal_neg_eq,neg_neg]
  refine ⟨hi.neg.congr heq.symm,?_⟩
  filter_upwards [ae_lt_top' hm hfin] with x hx
  simpa only [EReal.toENNReal_ne_top_iff,ne_eq,EReal.neg_eq_top_iff] using ne_of_lt hx

lemma profile_norm_integral_le {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    {C : ℝ} (hC : 0≤C) (hbound : (∫⁻ x in Ω,(-V x).toENNReal)≤ENNReal.ofReal C) :
    (∫ x in Ω, |(V x).toReal|)≤C := by
  have hfin : (∫⁻ x in Ω,(-V x).toENNReal)≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hi := (profile_integrable_of_lintegral_ne_top hΩ hV hneg hfin).1
  have heq : (fun x => |(V x).toReal|)=ᵐ[volume.restrict Ω]
      (fun x => (-V x).toENNReal.toReal) := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    rw [abs_of_nonpos (EReal.toReal_nonpos (hneg x hx)),
      EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x hx)),EReal.toReal_neg_eq]
  rw [integral_congr_ae heq,integral_toReal (usc_neg_toENNReal_aemeasurable hΩ hV)
    (ae_lt_top' (usc_neg_toENNReal_aemeasurable hΩ hV) hfin)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)
end SharpNodal.Profiles

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Distributional
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

theorem uniform_secondTaylor_remainder {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ x y,
    |f (x+y)-secondTaylorPolynomial f x (x+y)|≤C*‖y‖^3 := by
  have hd : Continuous (iteratedFDeriv ℝ 3 f) :=
    (hf.iteratedFDeriv_right (i:=3) (m:=0) (by exact WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).continuous
  obtain ⟨M,hM⟩ := hd.norm.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv (𝕜:=ℝ) 3).norm
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro x y
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n:=2) (x:=x) (y:=y)
    (fun t _ => (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).contDiffAt)
  have heq : f (x+y)-secondTaylorPolynomial f x (x+y)=
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)) := by
    simp only [show (2+1:ℕ)=3 from rfl,Finset.sum_range_succ,Finset.sum_range_zero,
      Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,zero_add,Nat.cast_one,Nat.cast_ofNat,
      inv_one,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,
      iteratedFDeriv_two_apply,smul_eq_mul] at ht
    dsimp only [secondTaylorPolynomial,centeredQuadratic]
    simp only [add_sub_cancel_left]
    linarith [ht]
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
      ≤ max 0 M*‖y‖^3 := by
    rw [← Real.norm_eq_abs]
    have hb : ∀ t ∈ uIoc (0:ℝ) 1,
        ‖(1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)‖≤ max 0 M*‖y‖^3 := by
      intro t ht
      simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1),mem_Ioc] at ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hder := (iteratedFDeriv ℝ 3 f (x+t • y)).le_opNorm (fun _ => y)
      have hnorm : ‖iteratedFDeriv ℝ 3 f (x+t • y)‖≤ max 0 M := (hM (mem_range_self (x+t • y))).trans (le_max_right _ _)
      have hs : (1-t)^2≤1 := by nlinarith [ht.1,ht.2]
      calc
        (1-t)^2*|iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
          ≤ 1*(max 0 M*‖y‖^3) := mul_le_mul hs (by simpa [Real.norm_eq_abs] using hder.trans (mul_le_mul_of_nonneg_right hnorm (by positivity))) (abs_nonneg _) (by positivity)
        _ = _ := one_mul _
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hpos : 0≤ max 0 M*‖y‖^3 := by positivity
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma planeCircleAverage_harmonic {f : Plane → ℝ} (hf : Smooth f)
    (hΔ : ∀x,euclideanLaplacian f x=0) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=f a := by
  have hg : ContDiff ℝ ∞ (f∘planeComplex.symm) :=
    hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hgΔ : ∀z,(Δ (f∘planeComplex.symm)) z=0 := by
    rw [laplacian_comp_isometry planeComplex.symm hf,← plane_laplacian_eq_mathlib hf]
    exact fun z => hΔ (planeComplex.symm z)
  have hh : HarmonicOnNhd (f∘planeComplex.symm) (Metric.closedBall (planeComplex a) |r|) := by
    intro z _
    refine ⟨hg.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)),?_⟩
    exact Filter.Eventually.of_forall hgΔ
  simpa only [planeCircleAverage,Function.comp_def,planeComplex.symm_apply_apply] using hh.circleAverage_eq

lemma planeCircleAverage_radiusSquare (a : Plane) (r : ℝ) :
    planeCircleAverage (radiusSquare a) a r=r^2 := by
  apply Real.circleAverage_const_on_circle
  intro z hz
  change ‖planeComplex.symm z-a‖^2=r^2
  rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
  rw [Metric.mem_sphere.mp hz,sq_abs]

lemma planeCircleAverage_secondTaylor {f : Plane → ℝ} (hf : Smooth f) (a : Plane) (r : ℝ) :
    planeCircleAverage (secondTaylorPolynomial f a) a r=
      f a+(r^2/4)*euclideanLaplacian f a := by
  let T := secondTaylorPolynomial f a
  let L := euclideanLaplacian f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have hL (x : Plane) : euclideanLaplacian T x=L := by
    change euclideanLaplacian (quadraticAffine (f a) (fderiv ℝ f a)
      (fderiv ℝ (fderiv ℝ f) a) a) x=euclideanLaplacian f a
    rw [laplacian_quadraticAffine (symmetric_hessian hf a)]
    unfold formTrace euclideanLaplacian
    apply Finset.sum_congr rfl
    intro i _
    exact hessian_on_basis hf a i i
  let q := fun x => T x+(-L/4)*radiusSquare a x
  have hq : Smooth q := hT.add (contDiff_const.mul (smooth_radiusSquare a))
  have hqΔ (x : Plane) : euclideanLaplacian q x=0 := by
    rw [show q=(fun x => T x+(-L/4)*radiusSquare a x) from rfl,
      laplacian_add hT (contDiff_const.mul (smooth_radiusSquare a)),
      laplacian_const_mul (smooth_radiusSquare a),hL]
    dsimp only
    rw [laplacian_radiusSquare]
    ring
  have havg := planeCircleAverage_harmonic hq hqΔ a r
  have hsplit : planeCircleAverage q a r=planeCircleAverage T a r+(-L/4)*r^2 := by
    unfold planeCircleAverage
    change Real.circleAverage (fun z => T (planeComplex.symm z)+(-L/4)*radiusSquare a (planeComplex.symm z)) _ r=_
    have h1 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => (-L/4)*radiusSquare a (planeComplex.symm z)) (planeComplex a) r :=
      ((contDiff_const.mul (smooth_radiusSquare a) : Smooth (fun x => (-L/4)*radiusSquare a x)).continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_add h1 h2]
    change _+Real.circleAverage ((-L/4) • (fun z => radiusSquare a (planeComplex.symm z))) (planeComplex a) r=_
    rw [Real.circleAverage_smul]
    change _+(-L/4)*planeCircleAverage (radiusSquare a) a r=_
    rw [planeCircleAverage_radiusSquare]
    rfl
  have hqa : q a=f a := by simp [q,T,secondTaylorPolynomial_self,radiusSquare]
  rw [hsplit,hqa] at havg
  change planeCircleAverage T a r=f a+r^2/4*L
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma planeCircleAverage_uniform_second_order {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ a r,
      |planeCircleAverage f a r-f a-(r^2/4)*euclideanLaplacian f a|≤C*|r|^3 := by
  obtain ⟨C,hC,hrem⟩ := uniform_secondTaylor_remainder hf hc
  refine ⟨C,hC,?_⟩
  intro a r
  let T := secondTaylorPolynomial f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have he : planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a =
    Real.circleAverage (fun z => f (planeComplex.symm z)-T (planeComplex.symm z)) (planeComplex a) r := by
    have h1 : CircleIntegrable (fun z => f (planeComplex.symm z)) (planeComplex a) r :=
      (hf.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_sub h1 h2]
    change planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a=
      planeCircleAverage f a r-planeCircleAverage (secondTaylorPolynomial f a) a r
    rw [planeCircleAverage_secondTaylor hf]
    ring
  rw [he]
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (((hf.continuous.sub hT.continuous).comp planeComplex.symm.continuous).abs).continuousOn.circleIntegrable'
  intro z hz
  have hr' : ‖planeComplex.symm z-a‖=|r| := by
    rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    exact Metric.mem_sphere.mp hz
  simpa only [Pi.abs_apply,add_sub_cancel,hr',T] using hrem a (planeComplex.symm z-a)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma submean_dual_lintegral {T : Type*} [MeasurableSpace T] {ν : Measure T} [SFinite ν]
    {f g : Plane → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {v : T → Plane} (hv : Measurable v)
    (hsub : ∀x,g x≠0 → (∫⁻ t,f (x+v t) ∂ν)≤f x) :
    (∫⁻ x,f x*(∫⁻ t,g (x-v t) ∂ν))≤∫⁻ x,f x*g x := by
  calc
    _ = ∫⁻ x,∫⁻ t,f x*g (x-v t) ∂ν := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hg.comp (measurable_const.sub hv))).symm
    _ = ∫⁻ t,(∫⁻ x,f x*g (x-v t)) ∂ν := by
      apply lintegral_lintegral_swap
      exact ((hf.comp measurable_fst).mul (hg.comp (measurable_fst.sub (hv.comp measurable_snd)))).aemeasurable
    _ = ∫⁻ t,(∫⁻ x,f (x+v t)*g x) ∂ν := by
      apply lintegral_congr
      intro t
      rw [← lintegral_add_right_eq_self (fun x => f x*g (x-v t)) (v t)]
      simp only [add_sub_cancel_right]
    _ = ∫⁻ x,∫⁻ t,f (x+v t)*g x ∂ν := by
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_snd.add (hv.comp measurable_fst))).mul (hg.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x,(∫⁻ t,f (x+v t) ∂ν)*g x := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const _ (hf.comp (measurable_const.add hv))
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : g x=0
      · simp [hx]
      · exact mul_le_mul' (hsub x hx) le_rfl
end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleVector_continuous (r : ℝ) : Continuous (circleVector r) :=
  planeComplex.symm.continuous.comp (continuous_circleMap 0 r)

lemma circleVector_norm (r t : ℝ) : ‖circleVector r t‖=|r| := by
  rw [circleVector,planeComplex.symm.norm_map]
  simpa only [zero_add] using norm_circleMap_zero r t

lemma planeCircleAverage_eq_integral (f : Plane → ℝ) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=∫t,f (a+circleVector r t) ∂circleParameterMeasure := by
  rw [planeCircleAverage,circleAverage_eq_integral_parameter]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Function.comp_def]
  congr 1
  simp [circleMap,circleVector]

lemma planeCircleAverage_continuous {f : Plane → ℝ} (hf : Continuous f) (r : ℝ) :
    Continuous (fun a => planeCircleAverage f a r) := by
  unfold planeCircleAverage Real.circleAverage
  change Continuous (((2*Real.pi)⁻¹:ℝ) • (fun a => ∫θ in (0:ℝ)..2*Real.pi, f (planeComplex.symm (circleMap (planeComplex a) r θ))))
  apply Continuous.const_smul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp (planeComplex.symm.continuous.comp (by fun_prop [circleMap]))

lemma planeCircleAverage_abs_le {f : Plane → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x,|f x|≤M) (a : Plane) (r : ℝ) : |planeCircleAverage f a r|≤M := by
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (hf.comp planeComplex.symm.continuous).abs.continuousOn.circleIntegrable'
  intro z _
  exact hM (planeComplex.symm z)

lemma integrable_mul_planeCircleAverage {w f : Plane → ℝ} (hw : Integrable w)
    (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun x => w x*planeCircleAverage f x r) := by
  obtain ⟨M,hM⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hc.norm
  apply hw.mul_bdd (planeCircleAverage_continuous hf r).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact planeCircleAverage_abs_le hf (fun y => by simpa only [← Real.norm_eq_abs] using hM (mem_range_self y)) x r

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem distributional_laplacian_nonpos_of_dual {w ψ : Plane → ℝ}
    (hw : Integrable w) (hwpos : ∀ᵐx,w x≥0) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    {δ : ℝ} (hδ : 0<δ)
    (hdual : ∀r,0 < r → r<δ →
      (∫x,w x*planeCircleAverage ψ x r)≤∫x,w x*ψ x) :
    (∫x,w x*euclideanLaplacian ψ x)≤0 := by
  obtain ⟨C,hC,herr⟩ := planeCircleAverage_uniform_second_order hψ hcψ
  have hiψ := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hiΔ := integrable_mul_continuous_compact hw (smooth_laplacian hψ).continuous (compact_laplacian hcψ)
  have hbound (r : ℝ) (hr : 0 < r) (hrδ : r<δ) :
      (∫x,w x*euclideanLaplacian ψ x)≤4*C*r*(∫x,w x) := by
    have hi := integrable_mul_planeCircleAverage hw hψ.continuous hcψ r
    have hpoint : ∀ᵐx,(r^2/4)*(w x*euclideanLaplacian ψ x)≤
        (w x*planeCircleAverage ψ x r-w x*ψ x)+(C*r^3)*w x := by
      filter_upwards [hwpos] with x hx
      have he := (abs_le.mp (herr x r)).1
      rw [abs_of_pos hr] at he
      have hh : r^2/4*euclideanLaplacian ψ x≤planeCircleAverage ψ x r-ψ x+C*r^3 := by linarith
      have hh' := mul_le_mul_of_nonneg_left hh hx
      nlinarith [hh']
    have hb := integral_mono_ae (hiΔ.const_mul (r^2/4)) ((hi.sub hiψ).add (hw.const_mul (C*r^3))) hpoint
    rw [integral_add' (hi.sub hiψ) (hw.const_mul (C*r^3)),integral_sub' hi hiψ,
      integral_const_mul,integral_const_mul] at hb
    have hd := hdual r hr hrδ
    apply (mul_le_mul_iff_of_pos_left (show 0 < r^2/4 by positivity)).mp
    calc
      (r^2/4)*(∫x,w x*euclideanLaplacian ψ x)≤C*r^3*(∫x,w x) := by linarith
      _ = (r^2/4)*(4*C*r*(∫x,w x)) := by ring
  have hlim : Tendsto (fun r : ℝ => 4*C*r*(∫x,w x)) (𝓝[>]0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => 4*C*r*(∫x,w x)) (𝓝 0) (𝓝 (4*C*0*(∫x,w x))) :=
      ((tendsto_const_nhds.mul (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0))).mul_const (∫x,w x))
    simpa using h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
  exact hbound r hr hrδ

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma circleVector_neg (r t : ℝ) : circleVector (-r) t= -circleVector r t := by
  simp [circleVector,circleMap]

lemma planeCircleAverage_eq_integral_sub (f : Plane → ℝ) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=∫t,f (a-circleVector r t) ∂circleParameterMeasure := by
  have hn : planeCircleAverage f a (-r)=planeCircleAverage f a r := by
    exact Real.circleAverage_neg_radius
  rw [← hn,planeCircleAverage_eq_integral]
  simp only [circleVector_neg,sub_eq_add_neg]

lemma lintegral_mul_ofReal_toReal {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (hfFin : (∫⁻x,f x)≠⊤) {g : Plane → ℝ}
    (hig : Integrable (fun x => (f x).toReal*g x)) (hgpos : ∀x,0≤g x) :
    (∫⁻x,f x*ENNReal.ofReal (g x))=ENNReal.ofReal (∫x,(f x).toReal*g x) := by
  rw [ofReal_integral_eq_lintegral_ofReal hig (Eventually.of_forall fun x => mul_nonneg ENNReal.toReal_nonneg (hgpos x))]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top' hf.aemeasurable hfFin] with x hx
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hx.ne]

lemma submean_dual_real {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (hfFin : (∫⁻x,f x)≠⊤) {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hψpos : ∀x,0≤ψ x) (r : ℝ)
    (hsub : ∀x,ψ x≠0 → (∫⁻t,f (x+circleVector r t) ∂circleParameterMeasure)≤f x) :
    (∫x,(f x).toReal*planeCircleAverage ψ x r)≤∫x,(f x).toReal*ψ x := by
  have hw : Integrable (fun x => (f x).toReal) := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfFin
  have havgpos (x : Plane) : 0≤planeCircleAverage ψ x r :=
    Real.circleAverage_nonneg_of_nonneg (fun z _ => hψpos (planeComplex.symm z))
  have hlin := submean_dual_lintegral hf (ENNReal.continuous_ofReal.comp hψ).measurable
    (circleVector_continuous r).measurable (fun x hx => hsub x (by contrapose! hx; simp [hx]))
  have hiψ := integrable_mul_continuous_compact hw hψ hcψ
  have hiavg := integrable_mul_planeCircleAverage hw hψ hcψ r
  have havg (x : Plane) : (∫⁻t,ENNReal.ofReal (ψ (x-circleVector r t)) ∂circleParameterMeasure)=
      ENNReal.ofReal (planeCircleAverage ψ x r) := by
    rw [planeCircleAverage_eq_integral_sub]
    exact (ofReal_integral_eq_lintegral_ofReal (circleParameter_integrable
      (hψ.comp (continuous_const.sub (circleVector_continuous r))))
      (Eventually.of_forall fun t => hψpos (x-circleVector r t))).symm
  simp only [Function.comp_def] at hlin
  simp_rw [havg] at hlin
  rw [lintegral_mul_ofReal_toReal hf hfFin hiavg havgpos,
    lintegral_mul_ofReal_toReal hf hfFin hiψ hψpos] at hlin
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (havgpos x)),
    ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (hψpos x))] using h

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma usc_density_indicator_measurable {Ω : Set Plane} {V : Plane → EReal}
    (hΩ : MeasurableSet Ω) (hV : UpperSemicontinuousOn V Ω) :
    Measurable (Ω.indicator (fun x => (-V x).toENNReal)) := by
  apply measurable_of_restrict_of_restrict_compl hΩ
  · have he : Ω.domRestrict (Ω.indicator (fun x => (-V x).toENNReal)) =
        (fun x : Ω => (-V x).toENNReal) := by
      funext x
      simp [Set.domRestrict]
    rw [he]
    exact EReal.continuous_toENNReal.measurable.comp
      (upperSemicontinuousOn_iff_restrict.mpr hV).measurable.neg
  · have he : Ωᶜ.domRestrict (Ω.indicator (fun x => (-V x).toENNReal)) =
        (fun _ : ↥(Ωᶜ) => (0:ℝ≥0∞)) := by
      funext x
      change Ω.indicator (fun y => (-V y).toENNReal) (x:Plane)=0
      exact Set.indicator_of_notMem x.property _
    rw [he]
    exact measurable_const

theorem profile_distribution_D6 {Ω : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hball : Metric.ball (0:Plane) 8⊆Ω)
    (hfin : (∫⁻x in Metric.ball (0:Plane) 8,(-V x).toENNReal)≠⊤)
    {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ⊆Metric.ball 0 6) (hψpos : ∀x,0≤ψ x) :
    0≤∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
  let f := (Metric.ball (0:Plane) 8).indicator (fun x => (-V x).toENNReal)
  have hfm : Measurable f := usc_density_indicator_measurable measurableSet_ball (hV.mono hball)
  have hff : (∫⁻x,f x)≠⊤ := by simpa only [f,lintegral_indicator measurableSet_ball] using hfin
  have hiw : Integrable (fun x => (f x).toReal) := integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hff
  have hd (r : ℝ) (hr : 0 < r) (hr1 : r<1) :
      (∫x,(f x).toReal*planeCircleAverage ψ x r)≤∫x,(f x).toReal*ψ x := by
    apply submean_dual_real hfm hff hψ.continuous hcψ hψpos r
    intro x hx
    have hx6 : x∈Metric.ball (0:Plane) 6 := hsψ (subset_tsupport ψ hx)
    have hb : Metric.closedBall x r⊆Metric.ball (0:Plane) 8 :=
      Metric.closedBall_subset_ball' (by change dist x 0<6 at hx6; linarith)
    have hx8 : x∈Metric.ball (0:Plane) 8 := hb (Metric.mem_closedBall_self hr.le)
    have hpt (t : ℝ) : planeComplex.symm (circleMap (planeComplex x) r t)=x+circleVector r t := by
      simp [circleVector,circleMap]
    have hm (t : ℝ) : x+circleVector r t∈Metric.closedBall x r := by
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,circleVector_norm,abs_of_pos hr]
    have hh := circle_submean hV hneg htest hr (hb.trans hball)
    simp_rw [hpt] at hh
    simpa only [f,Set.indicator_of_mem hx8,Set.indicator_of_mem (hb (hm _))] using hh
  have hh := distributional_laplacian_nonpos_of_dual hiw
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hψ hcψ (by norm_num : (0:ℝ)<1) hd
  have he : (∫x,(f x).toReal*euclideanLaplacian ψ x)=
      -(∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x) := by
    rw [← integral_neg,← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8
    · simp only [f,Set.indicator_of_mem hx]
      rw [EReal.toReal_toENNReal (by simpa using EReal.neg_le_neg_iff.mpr (hneg x (hball hx))),EReal.toReal_neg_eq]
      ring
    · simp only [f,Set.indicator_of_notMem hx,ENNReal.toReal_zero,zero_mul]
  rw [he] at hh
  exact neg_nonpos.mp hh

end SharpNodal.Profiles

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_RieszMeasure
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma smoothCompactTests_dominate (f : C_c(Plane,ℝ)) :
    ∃g : smoothCompactTests, 0 ≤ (g.val+f) := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:Plane)).mp f.hasCompactSupport.isBounded
  let R := max r 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let χ : ContDiffBump (0:Plane) := ⟨R,R+1,hR,by linarith⟩
  obtain ⟨M,hM⟩ := f.continuous.norm.bddAbove_range_of_hasCompactSupport f.hasCompactSupport.norm
  let N := max M 0
  let g : C_c(Plane,ℝ) := ⟨⟨fun x => N*χ x,χ.continuous.const_mul N⟩,χ.hasCompactSupport.mul_left⟩
  have hg : g∈smoothCompactTests := contDiff_const.mul χ.contDiff
  refine ⟨⟨g,hg⟩,?_⟩
  intro x
  change 0≤N*χ x+f x
  by_cases hx : x∈tsupport f
  · have hχ : χ x=1 := χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_left r 1) (hr hx))
    have hMb : |f x|≤M := by
      convert! hM (mem_range_self x) using 1
      all_goals try with_reducible_and_instances rfl
    have hb : |f x|≤N := hMb.trans (le_max_left _ _)
    rw [hχ,mul_one]
    linarith [(abs_le.mp hb).1]
  · rw [image_eq_zero_of_notMem_tsupport hx,add_zero]
    exact mul_nonneg (le_max_right _ _) χ.nonneg

theorem positive_smooth_tests_representable (F : smoothCompactTests →ₗ[ℝ] ℝ)
    (hF : ∀f : smoothCompactTests, (∀x,0≤f.val x) → 0≤F f) :
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      (∀f : smoothCompactTests,(∫x,f.val x ∂μ)=F f) ∧
      ∀(K : Set Plane),IsCompact K → ∀f : smoothCompactTests,
        (∀x,0≤f.val x) → (∀x∈K,f.val x=1) → μ K≤ENNReal.ofReal (F f) := by
  let p : C_c(Plane,ℝ) →ₗ.[ℝ] ℝ := ⟨smoothCompactTests,F⟩
  obtain ⟨g,hg,hgpos⟩ := riesz_extension compactTestsPositiveCone p
    (fun f hf => hF f hf) (fun f => smoothCompactTests_dominate f)
  let G : C_c(Plane,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ g (fun f hf => hgpos f hf)
  refine ⟨RealRMK.rieszMeasure G,inferInstance,?_,?_⟩
  · intro f
    rw [RealRMK.integral_rieszMeasure]
    exact hg f
  · intro K hK f hf hKf
    have hh := RealRMK.rieszMeasure_le_of_eq_one G hf hK hKf
    change RealRMK.rieszMeasure G K≤ENNReal.ofReal (g f.val) at hh
    rw [hg f] at hh
    exact hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem localized_laplacian_measure {w ζ : Plane → ℝ} {Ω O : Set Plane}
    (hw : Integrable w) (hζ : Smooth ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ⊆Ω) (hnζ : ∀x,0≤ζ x) (hoζ : ∀x∈O,ζ x=1)
    (hpos : ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
      (∀x,0≤ψ x) → 0≤∫x,w x*euclideanLaplacian ψ x) :
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      (∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆O →
        (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian ψ x) ∧
      ∀(K : Set Plane),IsCompact K → ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ →
        tsupport ψ⊆O → (∀x,0≤ψ x) → (∀x∈K,ψ x=1) →
        μ K≤ENNReal.ofReal (∫x,w x*euclideanLaplacian ψ x) := by
  let F := localizedLaplacianFunctional hw hζ hcζ
  have hF : ∀f : smoothCompactTests,(∀x,0≤f.val x) → 0≤F f := by
    intro f hf
    apply hpos (fun x => ζ x*f.val x) (hζ.mul f.property) hcζ.mul_right
    · exact tsupport_mul_subset_left.trans hsζ
    · exact fun x => mul_nonneg (hnζ x) (hf x)
  obtain ⟨μ,hμ,hrep,hbound⟩ := positive_smooth_tests_representable F hF
  have he (ψ : Plane → ℝ) (hsψ : tsupport ψ⊆O) : (fun x => ζ x*ψ x)=ψ := by
    funext x
    by_cases hx : ψ x=0
    · simp [hx]
    · rw [hoζ x (hsψ (subset_tsupport ψ hx)),one_mul]
  refine ⟨μ,hμ,?_,?_⟩
  · intro ψ hψ hcψ hsψ
    let f : smoothCompactTests := ⟨⟨⟨ψ,hψ.continuous⟩,hcψ⟩,hψ⟩
    have hh := hrep f
    change (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian (fun y => ζ y*ψ y) x at hh
    simpa only [he ψ hsψ] using hh
  · intro K hK ψ hψ hcψ hsψ hnψ hoψ
    let f : smoothCompactTests := ⟨⟨⟨ψ,hψ.continuous⟩,hcψ⟩,hψ⟩
    have hh := hbound K hK f hnψ hoψ
    change μ K≤ENNReal.ofReal (∫x,w x*euclideanLaplacian (fun y => ζ y*ψ y) x) at hh
    simpa only [he ψ hsψ] using hh

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integral_mul_le_norm_bound {w f : Plane → ℝ} (hw : Integrable w)
    {C : ℝ} (hf : ∀x,‖f x‖≤C) :
    (∫x,w x*f x)≤C*(∫x,‖w x‖) := by
  apply (le_abs_self _).trans
  have hh := norm_integral_le_of_norm_le (hw.norm.const_mul C)
    (f:=fun x => w x*f x) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,integral_const_mul] using hh

theorem local_positive_measure_uniform : ∃C : ℝ,0≤C ∧ ∀w : Plane → ℝ,
    Integrable w →
    (∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 6 →
      (∀x,0≤ψ x) → 0≤∫x,w x*euclideanLaplacian ψ x) →
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal (C*(∫x,‖w x‖)) ∧
      ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 (11/2) →
        (∫x,ψ x ∂μ)=∫x,w x*euclideanLaplacian ψ x := by
  let ζ : ContDiffBump (0:Plane) := ⟨11/2,23/4,by norm_num,by norm_num⟩
  let χ : ContDiffBump (0:Plane) := ⟨5,21/4,by norm_num,by norm_num⟩
  obtain ⟨M,hM⟩ := (smooth_laplacian χ.contDiff).continuous.norm.bddAbove_range_of_hasCompactSupport
    (compact_laplacian χ.hasCompactSupport).norm
  let C := max M 0
  have hbound (x : Plane) : ‖euclideanLaplacian χ x‖≤C := (hM (mem_range_self x)).trans (le_max_left _ _)
  refine ⟨C,le_max_right _ _,?_⟩
  intro w hw hpos
  have hsζ : tsupport (ζ : Plane → ℝ)⊆Metric.ball 0 6 := by
    rw [ζ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num : (23:ℝ)/4<6)
  have hsχ : tsupport (χ : Plane → ℝ)⊆Metric.ball 0 (11/2) := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num : (21:ℝ)/4<11/2)
  obtain ⟨μ,hμ,hrep,hboundμ⟩ := localized_laplacian_measure hw ζ.contDiff ζ.hasCompactSupport hsζ
    (fun _ => ζ.nonneg) (fun x hx => ζ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)) hpos
  have hh := hboundμ (Metric.closedBall 0 5) (isCompact_closedBall _ _) χ χ.contDiff χ.hasCompactSupport hsχ
    (fun _ => χ.nonneg) (fun x hx => χ.one_of_mem_closedBall hx)
  refine ⟨μ,hμ,hh.trans (ENNReal.ofReal_le_ofReal (integral_mul_le_norm_bound hw hbound)),hrep⟩

theorem profile_riesz_uniform : ∃C : ℝ,0≤C ∧ ∀V : Plane → EReal,
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) →
    FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∃μ : Measure Plane, IsFiniteMeasureOnCompacts μ ∧
      μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C ∧
      ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 (11/2) →
        (∫x,ψ x ∂μ)=∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
  obtain ⟨C,hC,hCprop⟩ := local_positive_measure_uniform
  refine ⟨C*(100*Real.pi),by positivity,?_⟩
  intro V hV hneg htest ⟨a,ha,hanchor⟩
  have hball : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hlin := profile_lintegral_D8 hV hneg htest ha hanchor
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hball)
    (fun x hx => hneg x (hball hx)) hfin).1
  let w := (Metric.ball (0:Plane) 8).indicator (fun x => (V x).toReal)
  have hw : Integrable w := hi.integrable_indicator measurableSet_ball
  have he (ψ : Plane → ℝ) : (∫x,w x*euclideanLaplacian ψ x)=
      ∫x in Metric.ball (0:Plane) 8,(V x).toReal*euclideanLaplacian ψ x := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx]
  have hpos (ψ : Plane → ℝ) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ⊆Metric.ball 0 6) (hnψ : ∀x,0≤ψ x) : 0≤∫x,w x*euclideanLaplacian ψ x := by
    rw [he]
    exact profile_distribution_D6 hV hneg htest hball hfin hψ hcψ hsψ hnψ
  obtain ⟨μ,hμ,hmass,hrep⟩ := hCprop w hw hpos
  have hnorm : (∫x,‖w x‖)≤100*Real.pi := by
    have heq : (fun x => ‖w x‖)=(Metric.ball (0:Plane) 8).indicator (fun x => |(V x).toReal|) := by
      funext x
      by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx,Real.norm_eq_abs]
    rw [heq,integral_indicator measurableSet_ball]
    exact profile_norm_integral_le measurableSet_ball (hV.mono hball) (fun x hx => hneg x (hball hx)) (by positivity) hlin
  refine ⟨μ,hμ,hmass.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnorm hC)),?_⟩
  intro ψ hψ hcψ hsψ
  exact (hrep ψ hψ hcψ hsψ).trans (he ψ)

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Potential
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma logDenom_pos {ε : ℝ} (hε : 0<ε) (x : Plane) : 0<logDenom ε x := by
  dsimp [logDenom]
  positivity

lemma smooth_logDenom (ε : ℝ) : Smooth (logDenom ε) := by
  exact (contDiff_id.norm_sq (𝕜:=ℝ)).add contDiff_const

lemma partial_logDenom (ε : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (logDenom ε) i x=2*x i := by
  have hd := ((hasFDerivAt_id (𝕜:=ℝ) x).norm_sq).add_const (ε^2)
  dsimp only [id_eq] at hd
  change (fderiv ℝ (fun y : Plane => ‖y‖^2+ε^2) x) (EuclideanSpace.single i 1)=_
  rw [hd.fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma smooth_regularizedLog {ε : ℝ} (hε : 0<ε) : Smooth (regularizedLog ε) := by
  exact ((smooth_logDenom ε).log (fun x => (logDenom_pos hε x).ne')).div_const 2

lemma partial_regularizedLog {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    coordPartial (regularizedLog ε) i x=x i/(logDenom ε x) := by
  have hd := (((smooth_logDenom ε).differentiable (by simp)).differentiableAt.hasFDerivAt.log
    (logDenom_pos hε x).ne').const_mul (1/2:ℝ)
  have he : regularizedLog ε=(fun y => (1/2:ℝ)*Real.log (logDenom ε y)) := by
    funext y; simp [regularizedLog,logDenom,div_eq_mul_inv,mul_comm]
  rw [he,coordPartial,hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  change (1/2:ℝ)*((logDenom ε x)⁻¹*coordPartial (logDenom ε) i x)=_
  rw [partial_logDenom]
  ring

lemma partial2_regularizedLog {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (regularizedLog ε) i) i x=
      (logDenom ε x)⁻¹-2*(x i)^2/(logDenom ε x)^2 := by
  have hD := ((smooth_logDenom ε).differentiable (by simp)).differentiableAt.hasFDerivAt (x:=x)
  have hinv := (hasDerivAt_inv (logDenom_pos hε x).ne').comp_hasFDerivAt x hD
  have hmul := (EuclideanSpace.proj i).hasFDerivAt.mul hinv
  rw [show coordPartial (regularizedLog ε) i=(fun y => y i*(logDenom ε y)⁻¹) from by
    funext y; rw [partial_regularizedLog hε]; rfl]
  change (fderiv ℝ _ x) (EuclideanSpace.single i 1)=_
  change HasFDerivAt (fun y : Plane => y i*(logDenom ε y)⁻¹) _ x at hmul
  rw [hmul.fderiv]
  change x i*(-((logDenom ε x)^2)⁻¹*coordPartial (logDenom ε) i x)+
    (logDenom ε x)⁻¹*(EuclideanSpace.single i 1) i=_
  rw [show (EuclideanSpace.single i (1:ℝ)) i=1 by simp,mul_one]
  rw [partial_logDenom]
  ring

lemma laplacian_regularizedLog {ε : ℝ} (hε : 0<ε) (x : Plane) :
    euclideanLaplacian (regularizedLog ε) x=2*ε^2/(‖x‖^2+ε^2)^2 := by
  simp only [euclideanLaplacian,partial2_regularizedLog hε,Fin.sum_univ_two]
  have hn : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    simpa only [Fin.sum_univ_two,Real.norm_eq_abs,sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
  dsimp [logDenom]
  have hd : ‖x‖^2+ε^2≠0 := (logDenom_pos hε x).ne'
  field_simp
  nlinarith

lemma integral_mul_laplacian {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    (∫x,f x*euclideanLaplacian g x)=(∫x,euclideanLaplacian f x*g x) := by
  simp only [euclideanLaplacian,Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_partial hf (smooth_partial hg i) (compact_partial hc i),
      integral_mul_partial (smooth_partial hf i) hg hc,neg_neg]
  · intro i _
    exact integrable_mul_compact_right (smooth_partial (smooth_partial hf i) i) hg hc
  · intro i _
    exact integrable_mul_compact_right hf (smooth_partial (smooth_partial hg i) i)
      (compact_partial (compact_partial hc i) i)

lemma regularizedLog_distribution {ε : ℝ} (hε : 0<ε) {ψ : Plane → ℝ}
    (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,regularizedLog ε x*euclideanLaplacian ψ x)=
      ∫x,(2*ε^2/(‖x‖^2+ε^2)^2)*ψ x := by
  rw [integral_mul_laplacian (smooth_regularizedLog hε) hψ hcψ]
  simp only [laplacian_regularizedLog hε]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_radial_ball_integral (f : ℝ → ℝ) (R : ℝ) :
    (∫x in Metric.ball (0:Plane) R,f ‖x‖)=2*Real.pi*∫r in Ioo 0 R,r*f r := by
  have he : (Metric.ball (0:Plane) R).indicator (fun x => f ‖x‖)=
       (fun x => (Iio R).indicator f ‖x‖) := by
    funext x
    simp [indicator,Metric.mem_ball,dist_zero_right]
  rw [← integral_indicator measurableSet_ball,he,integral_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one,smul_eq_mul,
    nsmul_eq_mul]
  have hv : (volume : Measure Plane).real (Metric.ball 0 1)=Real.pi := by
    rw [measureReal_def,EuclideanSpace.volume_ball_fin_two]
    norm_num
    exact Real.pi_pos.le
  rw [hv]
  have he' : (fun r : ℝ => r*(Iio R).indicator f r)=
      (Iio R).indicator (fun r => r*f r) := by
    funext r
    by_cases hr : r<R <;> simp [hr]
  rw [he',integral_indicator measurableSet_Iio]
  have hs : Iio R∩Ioi (0:ℝ)=Ioo 0 R := by ext r; exact and_comm
  rw [Measure.restrict_restrict measurableSet_Iio,hs]
  ring

lemma log_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => Real.log ‖x‖) (Metric.ball 0 R) := by
  rw [integrableOn_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,pow_one,smul_eq_mul]
  by_cases hR : 0≤R
  · have hi : IntervalIntegrable (fun r : ℝ => r*Real.log r) volume 0 R :=
      intervalIntegral.intervalIntegrable_log'.continuousOn_mul continuous_id.continuousOn
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hi).mono_set Ioo_subset_Ioc_self
  · have he : Ioo (0:ℝ) R=∅ := Ioo_eq_empty_of_le (le_of_not_ge hR)
    simp [he]

lemma regularizedLog_radial_mass {ε R : ℝ} (hε : 0<ε) (hR : 0≤R) :
    (∫x in Metric.ball (0:Plane) R,2*ε^2/(‖x‖^2+ε^2)^2)=
      2*Real.pi*(R^2/(R^2+ε^2)) := by
  rw [plane_radial_ball_integral (fun r => 2*ε^2/(r^2+ε^2)^2) R]
  congr 1
  have hd : ∀r : ℝ,HasDerivAt (fun r : ℝ => r^2/(r^2+ε^2))
      (r*(2*ε^2/(r^2+ε^2)^2)) r := by
    intro r
    have hden : r^2+ε^2≠0 := ne_of_gt (by positivity)
    convert! ((hasDerivAt_id r).pow 2).div (((hasDerivAt_id r).pow 2).add_const (ε^2)) hden using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one]
    field_simp
    ring
  have hc : Continuous (fun r : ℝ => r*(2*ε^2/(r^2+ε^2)^2)) := by
    fun_prop (disch := intro r; positivity)
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 R)]
  simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma logKernel_nonneg (ε : ℝ) (x : Plane) : 0≤logKernel ε x := by
  unfold logKernel
  positivity

lemma logKernel_eq (ε : ℝ) (x : Plane) :
    logKernel ε x=(2*Real.pi)⁻¹*(2*ε^2/(‖x‖^2+ε^2)^2) := by
  unfold logKernel
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma continuous_logKernel {ε : ℝ} (hε : 0<ε) : Continuous (logKernel ε) := by
  unfold logKernel
  fun_prop (disch := intro x; positivity)

lemma logKernel_uniform_away (u : Set Plane) (hu : IsOpen u) (h0 : (0:Plane)∈u) :
    TendstoUniformlyOn logKernel 0 (𝓝[>]0) (univ\u) := by
  obtain ⟨δ,hδ,hδu⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds h0)
  have hb (ε : ℝ) (x : Plane) (hx : x∈univ\u) :
      logKernel ε x≤ε^2/(Real.pi*δ^4) := by
    have hxδ : δ≤‖x‖ := le_of_not_gt (fun hh => hx.2 (hδu (by simpa [Metric.mem_ball,dist_zero_right] using hh)))
    unfold logKernel
    apply div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
    have hs : δ^2≤‖x‖^2+ε^2 := by nlinarith [sq_nonneg ε]
    have hs' : δ^4≤(‖x‖^2+ε^2)^2 := by nlinarith [sq_nonneg (‖x‖^2+ε^2-δ^2)]
    exact mul_le_mul_of_nonneg_left hs' Real.pi_pos.le
  have ht : Tendsto (fun ε : ℝ => ε^2/(Real.pi*δ^4)) (𝓝[>]0) (𝓝 0) := by
    have hh : Tendsto (fun ε : ℝ => ε^2/(Real.pi*δ^4)) (𝓝 0) (𝓝 (0^2/(Real.pi*δ^4))) :=
      (tendsto_id.pow 2).div_const _
    simpa using hh.mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [(tendsto_order.mp ht).2 η hη] with ε hε
  intro x hx
  simpa only [Pi.zero_apply,dist_zero_left,Real.norm_of_nonneg (logKernel_nonneg ε x)] using (hb ε x hx).trans_lt hε

lemma logKernel_mass_tendsto :
    Tendsto (fun ε : ℝ => ∫x in Metric.ball (0:Plane) 1,logKernel ε x) (𝓝[>]0) (𝓝 1) := by
  have he : (fun ε : ℝ => ∫x in Metric.ball (0:Plane) 1,logKernel ε x)=ᶠ[𝓝[>]0]
      (fun ε => (1+ε^2)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [logKernel_eq,integral_const_mul,regularizedLog_radial_mass hε (by norm_num : (0:ℝ)≤1),one_pow]
    field_simp
  apply Tendsto.congr' he.symm
  have hh : Tendsto (fun ε : ℝ => (1+ε^2)⁻¹) (𝓝 0) (𝓝 ((1+0^2)⁻¹)) := by
    apply Tendsto.inv₀
    · exact tendsto_const_nhds.add (tendsto_id.pow 2)
    · norm_num
  simpa using hh.mono_left nhdsWithin_le_nhds

lemma logKernel_test_tendsto {ψ : Plane → ℝ} (hψ : Continuous ψ) (hiψ : Integrable ψ) :
    Tendsto (fun ε : ℝ => ∫x,logKernel ε x*ψ x) (𝓝[>]0) (𝓝 (ψ 0)) := by
  have ht := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto (μ:=(volume:Measure Plane)) (g:=ψ) (φ:=logKernel)
    (x₀:=(0:Plane)) (s:=univ) (t:=Metric.ball (0:Plane) 1)
    MeasurableSet.univ measurableSet_ball (subset_univ _) (by simpa using Metric.ball_mem_nhds (0:Plane) (by norm_num : (0:ℝ)<1))
    (measure_ball_lt_top.ne) (Eventually.of_forall (fun _ _ _ => logKernel_nonneg _ _))
    logKernel_uniform_away logKernel_mass_tendsto
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using (continuous_logKernel hε).aestronglyMeasurable)
    (by simpa using hiψ) (by rw [nhdsWithin_univ]; convert! hψ.continuousAt (x:=(0:Plane)))
  simpa only [Measure.restrict_univ,smul_eq_mul] using ht

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma regularizedLog_bound {ε R : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hR : 0<R)
    {x : Plane} (hx : x∈Metric.ball 0 R) (hx0 : x≠0) :
    ‖regularizedLog ε x‖≤‖Real.log ‖x‖‖+‖Real.log (R^2+1)/2‖ := by
  have hxnorm : 0<‖x‖ := norm_pos_iff.mpr hx0
  have hxR : ‖x‖<R := by simpa [Metric.mem_ball,dist_zero_right] using hx
  have hlo : Real.log ‖x‖ ≤ regularizedLog ε x := by
    have hh := Real.log_le_log (sq_pos_of_pos hxnorm) (le_add_of_nonneg_right (sq_nonneg ε))
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [regularizedLog]
    linarith
  have hhi : regularizedLog ε x≤Real.log (R^2+1)/2 := by
    have hh : ‖x‖^2+ε^2≤R^2+1 := by nlinarith [norm_nonneg x]
    exact div_le_div_of_nonneg_right (Real.log_le_log (logDenom_pos hε x) hh) (by norm_num)
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log ‖x‖),abs_nonneg (Real.log (R^2+1)/2)]
  · linarith [le_abs_self (Real.log (R^2+1)/2),abs_nonneg (Real.log ‖x‖)]

lemma regularizedLog_tendsto {x : Plane} (hx : x≠0) :
    Tendsto (fun ε : ℝ => regularizedLog ε x) (𝓝[>]0) (𝓝 (Real.log ‖x‖)) := by
  have hn : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hh : Tendsto (fun ε : ℝ => Real.log (‖x‖^2+ε^2)/2) (𝓝 0)
      (𝓝 (Real.log (‖x‖^2+0^2)/2)) := by
    apply Tendsto.div_const
    apply Real.continuousAt_log (by simpa using hn) |>.tendsto.comp
    exact tendsto_const_nhds.add (tendsto_id.pow 2)
  simpa only [regularizedLog,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.log_pow,Nat.cast_ofNat,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hh.mono_left nhdsWithin_le_nhds

lemma regularizedLog_test_limit {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun ε : ℝ => ∫x,regularizedLog ε x*g x) (𝓝[>]0)
      (𝓝 (∫x,Real.log ‖x‖*g x)) := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hgM (x : Plane) : ‖g x‖≤M := hM (mem_range_self x)
  let B := fun x : Plane => (‖Real.log ‖x‖‖+‖Real.log (R^2+1)/2‖)*M
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=R))⟩
  have hiB : IntegrableOn B (Metric.ball 0 R) :=
    ((log_norm_integrableOn_ball R).norm.add (integrable_const _)).mul_const M
  have hne : ∀ᵐx : Plane,x≠0 := by simp [ae_iff]
  have hbound : ∀ᶠε : ℝ in 𝓝[>]0,∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),
      ‖regularizedLog ε x*g x‖≤B x := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with ε hε hε1
    filter_upwards [self_mem_ae_restrict measurableSet_ball,ae_restrict_of_ae hne] with x hx hx0
    rw [norm_mul]
    exact mul_le_mul (regularizedLog_bound hε hε1.le hR hx hx0) (hgM x) (norm_nonneg _) (by positivity)
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (F:=fun ε x => regularizedLog ε x*g x) (f:=fun x => Real.log ‖x‖*g x)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using
      ((smooth_regularizedLog hε).continuous.mul hg).aestronglyMeasurable)
    hbound hiB
    (by filter_upwards [ae_restrict_of_ae hne] with x hx using (regularizedLog_tendsto hx).mul_const (g x))
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  simpa only [he] using ht

lemma logarithmic_fundamental_solution {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,Real.log ‖x‖*euclideanLaplacian ψ x)=2*Real.pi*ψ 0 := by
  have hl := regularizedLog_test_limit (smooth_laplacian hψ).continuous (compact_laplacian hcψ)
  have hr := (logKernel_test_tendsto hψ.continuous (hψ.continuous.integrable_of_hasCompactSupport hcψ)).const_mul (2*Real.pi)
  have he : (fun ε : ℝ => ∫x,regularizedLog ε x*euclideanLaplacian ψ x)=ᶠ[𝓝[>]0]
      (fun ε => (2*Real.pi)*(∫x,logKernel ε x*ψ x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [regularizedLog_distribution hε hψ hcψ,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [logKernel_eq]
    have hp : 2*Real.pi≠0 := by positivity
    field_simp
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma log_translate_local {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    IntegrableOn (fun x : Plane => Real.log ‖x-z‖) (Metric.ball 0 R) ∧
    (∫x in Metric.ball (0:Plane) R,‖Real.log ‖x-z‖‖) ≤
      ∫x in Metric.ball (0:Plane) (R+S),‖Real.log ‖x‖‖ := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator (fun x => Real.log ‖x‖)
  have hiF : Integrable F := (log_norm_integrableOn_ball (R+S)).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hiF.aestronglyMeasurable |>.mpr hiF
  have he : ∀x∈Metric.ball (0:Plane) R,Real.log ‖x-z‖=F (x-z) := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hnorm : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add hxR hz)
    simp only [F,indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)]
  refine ⟨hit.integrableOn.congr_fun (fun x hx => (he x hx).symm) measurableSet_ball,?_⟩
  calc
    _ = ∫x in Metric.ball (0:Plane) R,‖F (x-z)‖ := setIntegral_congr_fun measurableSet_ball (fun x hx => congrArg norm (he x hx))
    _ ≤ ∫x,‖F (x-z)‖ := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => norm_nonneg _)) hit.norm
    _ = ∫x,‖F x‖ := integral_sub_right_eq_self (fun x => ‖F x‖) z
    _ = _ := by
      simp only [F,norm_indicator_eq_indicator_norm,integral_indicator measurableSet_ball]

lemma logPotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    Integrable (fun p : Plane×Plane => Real.log ‖p.1-p.2‖)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
  have hm : Measurable (fun p : Plane×Plane => Real.log ‖p.1-p.2‖) :=
    Real.measurable_log.comp ((measurable_fst.sub measurable_snd).norm)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [hs] with z hz using (log_translate_local (R:=R) hz).1
  · apply (integrable_const (∫x in Metric.ball (0:Plane) (R+S),‖Real.log ‖x‖‖)).mono'
      hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hs] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact (log_translate_local (R:=R) hz).2

lemma aeLogPotential_integrableOn (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) : IntegrableOn (aeLogPotential ν) (Metric.ball 0 R) :=
  (logPotential_prod_integrable ν hs R).integral_prod_left

lemma partial_translate {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) (i : Fin 2) :
    coordPartial (fun y => f (y+z)) i x=coordPartial f i (x+z) := by
  have hh := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).add_const z)
  change (fderiv ℝ (fun y => f (y+z)) x) _ = _
  have he : fderiv ℝ (fun y => f (y+z)) x=fderiv ℝ f (x+z) := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
  rw [he]
  rfl

lemma laplacian_translate {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) :
    euclideanLaplacian (fun y => f (y+z)) x=euclideanLaplacian f (x+z) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (fun y => f (y+z)) i=(fun y => coordPartial f i (y+z)) from funext (fun y => partial_translate hf z y i)]
  exact partial_translate (smooth_partial hf i) z x i

lemma logarithmic_fundamental_solution_translate {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (z : Plane) :
    (∫x,Real.log ‖x-z‖*euclideanLaplacian ψ x)=2*Real.pi*ψ z := by
  rw [← integral_add_right_eq_self (fun x => Real.log ‖x-z‖*euclideanLaplacian ψ x) z]
  simp only [add_sub_cancel_right]
  have hs : Smooth (fun x => ψ (x+z)) := hψ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun x => ψ (x+z)) := hcψ.comp_homeomorph (Homeomorph.addRight z)
  simpa only [laplacian_translate hψ,zero_add] using logarithmic_fundamental_solution hs hc

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma aeLogPotential_norm_bound (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    (∫x in Metric.ball (0:Plane) R,‖aeLogPotential ν x‖) ≤
      ν.real univ*(∫x in Metric.ball (0:Plane) (R+S),‖Real.log ‖x‖‖) := by
  have hp := logPotential_prod_integrable ν hs R
  calc
    _ ≤ ∫x in Metric.ball (0:Plane) R,∫z,‖Real.log ‖x-z‖‖ ∂ν :=
      integral_mono_ae hp.integral_prod_left.norm hp.integral_norm_prod_left
        (Eventually.of_forall (fun x => norm_integral_le_integral_norm _))
    _ = ∫z,(∫x in Metric.ball (0:Plane) R,‖Real.log ‖x-z‖‖) ∂ν := integral_integral_swap hp.norm
    _ ≤ ∫_z,(∫x in Metric.ball (0:Plane) (R+S),‖Real.log ‖x‖‖) ∂ν := by
      apply integral_mono_ae hp.integral_norm_prod_right (integrable_const _)
      filter_upwards [hs] with z hz using (log_translate_local (R:=R) hz).2
    _ = _ := by simp only [integral_const,smul_eq_mul]

lemma aeLogPotential_test_swap (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    (∫x,aeLogPotential ν x*g x) = ∫z,(∫x,Real.log ‖x-z‖*g x) ∂ν := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  have hp := logPotential_prod_integrable ν hs R
  have hint : Integrable (fun p : Plane×Plane => Real.log ‖p.1-p.2‖*g p.1)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
    apply (hp.norm.mul_const M).mono'
      (((Real.measurable_log.comp ((measurable_fst.sub measurable_snd).norm)).mul (hg.measurable.comp measurable_fst)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖Real.log ‖p.1-p.2‖*g p.1‖≤‖Real.log ‖p.1-p.2‖‖*M
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM (mem_range_self p.1)) (norm_nonneg _)
  rw [← he (aeLogPotential ν)]
  calc
    _ = ∫x in Metric.ball (0:Plane) R,∫z,Real.log ‖x-z‖*g x ∂ν := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x _
      simp only [integral_mul_const,aeLogPotential]
    _ = ∫z,(∫x in Metric.ball (0:Plane) R,Real.log ‖x-z‖*g x) ∂ν := integral_integral_swap hint
    _ = _ := by simp only [he]

lemma aeLogPotential_distribution (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,aeLogPotential ν x*euclideanLaplacian ψ x)=2*Real.pi*(∫z,ψ z ∂ν) := by
  rw [aeLogPotential_test_swap ν hs (smooth_laplacian hψ).continuous (compact_laplacian hcψ)]
  simp only [logarithmic_fundamental_solution_translate hψ hcψ,integral_const_mul]

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Parametrix
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma smooth_parametrixSmoothLog : Smooth parametrixSmoothLog := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact (contDiff_id.norm_sq (𝕜:=ℝ)).add (parametrixInner.contDiff.pow 2)
  · intro x
    by_cases hx : x=0
    · subst x
      have ho : parametrixInner (0:Plane)=1 := parametrixInner.one_of_mem_closedBall (by simp [parametrixInner,Metric.mem_closedBall])
      simp [ho]
    · have hpos : 0<‖x‖^2+(parametrixInner x)^2 :=
        add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx)) (sq_nonneg _)
      exact hpos.ne'

lemma smooth_parametrixCorrection : Smooth parametrixCorrection :=
  (parametrixCutoff.contDiff.sub contDiff_const).mul smooth_parametrixSmoothLog
lemma smooth_parametrixKernel : Smooth parametrixKernel := smooth_laplacian smooth_parametrixCorrection

lemma parametrixSmoothLog_eq {x : Plane} (hx : (1/8:ℝ)≤‖x‖) :
    parametrixSmoothLog x=Real.log ‖x‖ := by
  have hz : parametrixInner x=0 := parametrixInner.zero_of_le_dist (by simpa [parametrixInner,dist_zero_right] using hx)
  simp only [parametrixSmoothLog,hz,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.log_pow,Nat.cast_ofNat]
  ring

lemma logParametrix_eq (x : Plane) :
    logParametrix x=Real.log ‖x‖+parametrixCorrection x := by
  by_cases hx : ‖x‖≤(1/8:ℝ)
  · have ho : parametrixCutoff x=1 := parametrixCutoff.one_of_mem_closedBall (by simpa [parametrixCutoff,Metric.mem_closedBall,dist_zero_right] using hx)
    simp [logParametrix,parametrixCorrection,ho]
  · rw [parametrixCorrection,parametrixSmoothLog_eq (le_of_not_ge hx)]
    dsimp [logParametrix]; ring

lemma laplacian_of_log_germ {f : Plane → ℝ} (hf : Smooth f) {x : Plane} (hx : x≠0)
    (he : f=ᶠ[𝓝 x](fun y => Real.log ‖y‖)) : euclideanLaplacian f x=0 := by
  let g : ℂ → ℝ := f∘planeComplex.symm
  have hg : ContDiff ℝ ∞ g := hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hh : HarmonicAt (fun z : ℂ => Real.log ‖z‖) (planeComplex x) :=
    analyticAt_id.harmonicAt_log_norm (by simpa using hx)
  have he' : g=ᶠ[𝓝 (planeComplex x)](fun z : ℂ => Real.log ‖z‖) := by
    have htend : Tendsto planeComplex.symm (𝓝 (planeComplex x)) (𝓝 x) := by
      simpa only [planeComplex.symm_apply_apply] using (planeComplex.symm.continuous.continuousAt (x:=planeComplex x)).tendsto
    have ht := he.comp_tendsto htend
    filter_upwards [ht] with z hz
    simpa only [g,Function.comp_apply,LinearIsometryEquiv.norm_map] using hz
  have hhg : HarmonicAt g (planeComplex x) := (harmonicAt_congr_nhds he').mpr hh
  have hzero := hhg.2.self_of_nhds
  have heq := congrFun (laplacian_comp_isometry planeComplex.symm hf) (planeComplex x)
  rw [← plane_laplacian_eq_mathlib hf] at heq
  simpa only [g,Function.comp_apply,planeComplex.symm_apply_apply,Pi.zero_apply] using heq.symm.trans hzero

lemma parametrixKernel_zero {x : Plane} (hx : (1/4:ℝ)<‖x‖) : parametrixKernel x=0 := by
  have he : (fun y => -parametrixCorrection y)=ᶠ[𝓝 x](fun y => Real.log ‖y‖) := by
    filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hx))] with y hy
    have hz : parametrixCutoff y=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hy.le)
    rw [parametrixCorrection,hz,parametrixSmoothLog_eq (by linarith)]
    ring
  have hh := laplacian_of_log_germ smooth_parametrixCorrection.neg (by intro h; norm_num [h] at hx) he
  have heq : (fun y => -parametrixCorrection y)=(fun y => (-1:ℝ)*parametrixCorrection y) := by funext y; ring
  rw [heq,laplacian_const_mul smooth_parametrixCorrection] at hh
  simpa only [neg_one_mul,neg_eq_zero,parametrixKernel] using hh

lemma compact_parametrixKernel : HasCompactSupport parametrixKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4:ℝ))
  intro x hx
  exact parametrixKernel_zero (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)

lemma logParametrix_zero {x : Plane} (hx : (1/4:ℝ)≤‖x‖) : logParametrix x=0 := by
  have hz : parametrixCutoff x=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hx)
  simp [logParametrix,hz]

lemma integral_parametrix_identity {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,logParametrix x*euclideanLaplacian ψ x)=2*Real.pi*ψ 0+(∫x,parametrixKernel x*ψ x) := by
  have hlog : Integrable (fun x : Plane => Real.log ‖x‖*euclideanLaplacian ψ x) := by
    obtain ⟨R,hR,hzero⟩ := (compact_laplacian hcψ).exists_pos_le_norm
    obtain ⟨M,hM⟩ := (smooth_laplacian hψ).continuous.norm.bddAbove_range_of_hasCompactSupport (compact_laplacian hcψ).norm
    have hi := (IntegrableOn.integrable_indicator ((log_norm_integrableOn_ball R).norm) measurableSet_ball).mul_const M
    apply hi.mono' ((Real.measurable_log.comp measurable_norm).mul (smooth_laplacian hψ).continuous.measurable).aestronglyMeasurable
    filter_upwards [] with x
    change ‖Real.log ‖x‖*euclideanLaplacian ψ x‖≤((Metric.ball (0:Plane) R).indicator (fun x => ‖Real.log ‖x‖‖) x)*M
    by_cases hx : x∈Metric.ball (0:Plane) R
    · rw [indicator_of_mem hx,norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (mem_range_self x)) (norm_nonneg _)
    · rw [hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx),mul_zero,norm_zero,indicator_of_notMem hx,zero_mul]
  have hc : Integrable (fun x => parametrixCorrection x*euclideanLaplacian ψ x) :=
    integrable_mul_compact_right smooth_parametrixCorrection (smooth_laplacian hψ) (compact_laplacian hcψ)
  simp_rw [logParametrix_eq,add_mul]
  rw [integral_add hlog hc,logarithmic_fundamental_solution hψ hcψ,integral_mul_laplacian smooth_parametrixCorrection hψ hcψ]
  rfl
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rconv_eq (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f y*g (x-y) := rfl
lemma rconv_swap (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f (x-y)*g y :=
  convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)

lemma smooth_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Smooth (rconv f g) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hg

lemma partial_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    coordPartial (rconv f g) i=rconv f (coordPartial g i) := by
  funext x
  have hh := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable (hg.of_le (by simp : (1:ℕ∞ω)≤(∞:ℕ∞ω))) x
  have he : fderiv ℝ (rconv f g) x=(f ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane,volume] fderiv ℝ g) x := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
  change (fderiv ℝ (rconv f g) x) _=_
  rw [he,convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable
    (hc.fderiv ℝ) ((hg.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).continuous)]
  rfl

lemma laplacian_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    euclideanLaplacian (rconv f g)=rconv f (euclideanLaplacian g) := by
  funext x
  simp only [euclideanLaplacian,partial_rconv hf hg hc,
    partial_rconv hf (smooth_partial hg _) (compact_partial hc _)]
  simp only [rconv_eq,euclideanLaplacian,Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact (compact_partial (compact_partial hc i) i).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable (smooth_partial (smooth_partial hg i) i).continuous x

lemma partial_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) (i : Fin 2) :
    coordPartial (fun y => f (z-y)) i x= -coordPartial f i (z-x) := by
  have hh := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_sub z)
  have he : fderiv ℝ (fun y => f (z-y)) x= -(fderiv ℝ f (z-x)) := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp
  change (fderiv ℝ (fun y => f (z-y)) x) _=_
  rw [he]
  rfl

lemma laplacian_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) :
    euclideanLaplacian (fun y => f (z-y)) x=euclideanLaplacian f (z-x) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hrf : Smooth (fun y => coordPartial f i (z-y)) := (smooth_partial hf i).comp (contDiff_const.sub contDiff_id)
  rw [show coordPartial (fun y => f (z-y)) i=(fun y => -coordPartial f i (z-y)) from funext (fun y => partial_reflection hf z y i),
    partial_neg hrf,
    partial_reflection (smooth_partial hf i),neg_neg]

lemma compact_reflection {f : Plane → ℝ} (hc : HasCompactSupport f) (z : Plane) :
    HasCompactSupport (fun y => f (z-y)) := by
  convert! hc.comp_homeomorph ((Homeomorph.neg Plane).trans (Homeomorph.addRight z)) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  congr 1
  change z-y= -y+z
  abel

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integrable_logParametrix : Integrable logParametrix := by
  let F := (Metric.ball (0:Plane) 1).indicator (fun x => Real.log ‖x‖)
  have hi : Integrable F := (log_norm_integrableOn_ball 1).integrable_indicator measurableSet_ball
  have he : logParametrix=(fun x => parametrixCutoff x*F x) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 1
    · simp [logParametrix,F,hx]
    · have hn : 1≤‖x‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx
      rw [logParametrix_zero (by linarith)]
      simp [F,hx]
  rw [he]
  exact hi.bdd_mul parametrixCutoff.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (parametrixCutoff.nonneg)] using parametrixCutoff.le_one))

lemma laplacian_parametrix_convolution {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) (x : Plane) :
    euclideanLaplacian (rconv logParametrix ψ) x=2*Real.pi*ψ x+rconv parametrixKernel ψ x := by
  rw [laplacian_rconv integrable_logParametrix hψ hcψ,rconv_eq,rconv_eq]
  have hs : Smooth (fun y => ψ (x-y)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hh := integral_parametrix_identity hs (compact_reflection hcψ x)
  simpa only [laplacian_reflection hψ,sub_zero] using hh

lemma parametrix_convolution_support {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball (0:Plane) 3) :
    HasCompactSupport (rconv logParametrix ψ) ∧ tsupport (rconv logParametrix ψ)⊆Metric.ball (0:Plane) 4 := by
  have hzero : ∀x, (13/4:ℝ)≤‖x‖ → rconv logParametrix ψ x=0 := by
    intro x hx
    rw [rconv_eq]
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    change logParametrix y*ψ (x-y)=0
    by_cases hy : (1/4:ℝ)≤‖y‖
    · rw [logParametrix_zero hy,zero_mul]
    · have hy' : ‖y‖<(1/4:ℝ) := lt_of_not_ge hy
      have hn : 3<‖x-y‖ := by have ht := norm_sub_norm_le x y; linarith
      have hz : ψ (x-y)=0 := image_eq_zero_of_notMem_tsupport (fun ht => by
        have hb : ‖x-y‖<3 := by simpa only [Metric.mem_ball,dist_zero_right] using hs ht
        linarith)
      rw [hz,mul_zero]
  have hts : tsupport (rconv logParametrix ψ)⊆Metric.closedBall (0:Plane) (13/4:ℝ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hn
    have hn' : (13/4:ℝ)<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn
    exact hx (hzero x hn'.le)
  refine ⟨(isCompact_closedBall (0:Plane) (13/4:ℝ)).of_isClosed_subset (isClosed_tsupport _) hts,?_⟩
  intro x hx
  have hn : ‖x‖≤(13/4:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hts hx
  change dist x 0<4
  rw [dist_zero_right]
  linarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rconv_duality {w φ K : Plane → ℝ} (hw : Integrable w) (hφ : Integrable φ)
    (hK : Continuous K) (hcK : HasCompactSupport K) :
    (∫x,w x*rconv K φ x)=(∫x,rconv w (fun y => K (-y)) x*φ x) := by
  obtain ⟨M,hM⟩ := hK.norm.bddAbove_range_of_hasCompactSupport hcK.norm
  have hp : Integrable (fun p : Plane×Plane => w p.1*K (p.1-p.2)*φ p.2) (volume.prod volume) := by
    apply ((hw.norm.mul_prod hφ.norm).mul_const M).mono'
      ((hw.aestronglyMeasurable.comp_fst.mul (hK.measurable.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul hφ.aestronglyMeasurable.comp_snd)
    filter_upwards [] with p
    change ‖w p.1*K (p.1-p.2)*φ p.2‖≤(‖w p.1‖*‖φ p.2‖)*M
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ‖w p.1‖*M*‖φ p.2‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM (mem_range_self (p.1-p.2))) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ∫x,∫z,w x*K (x-z)*φ z := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [rconv_swap,← integral_const_mul,mul_assoc]
    _ = ∫z,∫x,w x*K (x-z)*φ z := integral_integral_swap hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [rconv_eq,neg_sub,integral_mul_const]

lemma norm_rconv_le {w K : Plane → ℝ} (hw : Integrable w)
    (hK : Continuous K) (hcK : HasCompactSupport K) {C : ℝ} (hC : ∀x,‖K x‖≤C) (x : Plane) :
    ‖rconv w K x‖≤C*(∫y,‖w y‖) := by
  have hi := hcK.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hw.locallyIntegrable hK x
  calc
    _ ≤ ∫y,‖w y*K (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫y,‖w y‖*C := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const C)
      filter_upwards [] with y
      change ‖w y*K (x-y)‖≤‖w y‖*C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (x-y)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const,mul_comm]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma smooth_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) :
    Smooth (weylRepresentative w) := by
  apply contDiff_const.mul
  exact smooth_rconv hw (smooth_parametrixKernel.comp contDiff_id.neg)
    (compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane))

lemma weylRepresentative_test {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) {ψ : Plane → ℝ}
    (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 3) :
    (∫x,w x*ψ x)=(∫x,weylRepresentative w x*ψ x) := by
  have hiψ : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hcψ
  have hiK : Integrable parametrixKernel := smooth_parametrixKernel.continuous.integrable_of_hasCompactSupport compact_parametrixKernel
  have hcv : Smooth (rconv parametrixKernel ψ) := smooth_rconv hiK hψ hcψ
  have hccv : HasCompactSupport (rconv parametrixKernel ψ) :=
    compact_parametrixKernel.convolution (ContinuousLinearMap.mul ℝ ℝ) hcψ
  have hi1 := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hi2 := integrable_mul_continuous_compact hw hcv.continuous hccv
  obtain ⟨hcQ,hsQ⟩ := parametrix_convolution_support hsψ
  have h0 := hweak (rconv logParametrix ψ) (smooth_rconv integrable_logParametrix hψ hcψ) hcQ hsQ
  simp_rw [laplacian_parametrix_convolution hψ hcψ] at h0
  have he : (fun x => w x*(2*Real.pi*ψ x+rconv parametrixKernel ψ x))=
      (fun x => (2*Real.pi)*(w x*ψ x)+w x*rconv parametrixKernel ψ x) := by funext x; ring
  rw [he,integral_add (hi1.const_mul _) hi2,integral_const_mul,
    rconv_duality hw hiψ smooth_parametrixKernel.continuous compact_parametrixKernel] at h0
  have he' : (fun x => weylRepresentative w x*ψ x)=
      (fun x => -(2*Real.pi)⁻¹*(rconv w (fun y => parametrixKernel (-y)) x*ψ x)) := by
    funext x; dsimp [weylRepresentative]; ring
  rw [he',integral_const_mul]
  have hp : 2*Real.pi≠0 := by positivity
  field_simp
  linarith

lemma weylRepresentative_ae {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) :
    ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → w x=weylRepresentative w x := by
  have hh := smooth_weylRepresentative hw
  have ha := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hw.locallyIntegrable.sub hh.continuous.locallyIntegrable).locallyIntegrableOn (Metric.ball (0:Plane) 3))
    (fun ψ hψ hcψ hsψ => ?_)
  · filter_upwards [ha] with x hx hmem
    exact sub_eq_zero.mp (hx hmem)
  have hiw := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hih := integrable_mul_compact_right hh hψ hcψ
  have he : (fun x => ψ x • (w x-weylRepresentative w x))=
      (fun x => w x*ψ x-weylRepresentative w x*ψ x) := by funext x; simp only [smul_eq_mul]; ring
  change (∫x,ψ x • (w x-weylRepresentative w x))=0
  rw [he,integral_sub hiw hih,weylRepresentative_test hw hweak hψ hcψ hsψ,sub_self]

lemma weakHarmonic_smooth {h : Plane → ℝ} (hh : Smooth h) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hweak : WeakHarmonicOn h Ω) :
    ∀x∈Ω,euclideanLaplacian h x=0 := by
  have hΔ := smooth_laplacian hh
  have ha : ∀ᵐx : Plane,x∈Ω → euclideanLaplacian h x=0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hΔ.continuous.locallyIntegrable.locallyIntegrableOn Ω)
    intro ψ hψ hcψ hsψ
    have hi := hweak ψ hψ hcψ hsψ
    rw [integral_mul_laplacian hh hψ hcψ] at hi
    simpa only [smul_eq_mul,mul_comm] using hi
  have hae : euclideanLaplacian h=ᵐ[volume.restrict Ω]0 := by
    filter_upwards [ae_restrict_of_ae ha,self_mem_ae_restrict hΩ.measurableSet] with x hx hmem
    exact hx hmem
  exact Measure.eqOn_open_of_ae_eq hae hΩ hΔ.continuous.continuousOn continuous_const.continuousOn

lemma weylRepresentative_harmonic {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) :
    ∀x∈Metric.ball (0:Plane) 3,euclideanLaplacian (weylRepresentative w) x=0 := by
  apply weakHarmonic_smooth (smooth_weylRepresentative hw) Metric.isOpen_ball
  intro ψ hψ hcψ hsψ
  have he : (fun x => weylRepresentative w x*euclideanLaplacian ψ x)=ᵐ[volume]
      (fun x => w x*euclideanLaplacian ψ x) := by
    filter_upwards [weylRepresentative_ae hw hweak] with x hx
    by_cases hm : x∈Metric.ball (0:Plane) 3
    · rw [hx hm]
    · have hz : euclideanLaplacian ψ x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hm (hsψ (laplacian_tsupport_subset ψ ht)))
      simp only [hz,mul_zero]
  rw [integral_congr_ae he]
  apply hweak ψ hψ hcψ
  intro x hx
  exact Metric.ball_subset_ball (by norm_num : (3:ℝ)≤4) (hsψ hx)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma partial_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) (i : Fin 2) (x : Plane) :
    coordPartial (weylRepresentative w) i x = -(2*Real.pi)⁻¹*
      rconv w (coordPartial (fun y => parametrixKernel (-y)) i) x := by
  have hk : Smooth (fun y => parametrixKernel (-y)) := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport (fun y => parametrixKernel (-y)) := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  change coordPartial (fun y => -(2*Real.pi)⁻¹*rconv w (fun z => parametrixKernel (-z)) y) i x = _
  rw [partial_const_mul (smooth_rconv hw hk hc),partial_rconv hw hk hc]

lemma partial2_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (weylRepresentative w) i) j x = -(2*Real.pi)⁻¹*
      rconv w (coordPartial (coordPartial (fun y => parametrixKernel (-y)) i) j) x := by
  have hk : Smooth (fun y => parametrixKernel (-y)) := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport (fun y => parametrixKernel (-y)) := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  have he : coordPartial (weylRepresentative w) i =
      (fun x => -(2*Real.pi)⁻¹*rconv w (coordPartial (fun y => parametrixKernel (-y)) i) x) := by
    funext x; exact partial_weylRepresentative hw i x
  rw [he,partial_const_mul (smooth_rconv hw (smooth_partial hk i) (compact_partial hc i)),
    partial_rconv hw (smooth_partial hk i) (compact_partial hc i)]

lemma uniform_weyl_derivative_bounds : ∃C : ℝ,0≤C ∧ ∀w : Plane → ℝ, Integrable w →
    ∀x : Plane, (∀i : Fin 2,|coordPartial (weylRepresentative w) i x|≤C*∫y,‖w y‖) ∧
      (∀i j : Fin 2,|coordPartial (coordPartial (weylRepresentative w) i) j x|≤C*∫y,‖w y‖) := by
  let K := fun y : Plane => parametrixKernel (-y)
  have hk : Smooth K := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport K := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  have hbound (f : Plane → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) : ∃C : ℝ,0≤C ∧ ∀x,‖f x‖≤C := by
    obtain ⟨C,hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hcf.norm
    refine ⟨max 0 C,le_max_left _ _,fun x => ?_⟩
    exact (hC (mem_range_self x)).trans (le_max_right _ _)
  choose C₁ hC₁p hC₁ using fun i : Fin 2 => hbound (coordPartial K i) (smooth_partial hk i).continuous (compact_partial hc i)
  choose C₂ hC₂p hC₂ using fun i j : Fin 2 => hbound (coordPartial (coordPartial K i) j)
    (smooth_partial (smooth_partial hk i) j).continuous (compact_partial (compact_partial hc i) j)
  let C := (∑i,C₁ i)+(∑i,∑j,C₂ i j)
  have hCp : 0≤C := add_nonneg (Finset.sum_nonneg (fun i _ => hC₁p i))
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j)))
  have hb₁ (i : Fin 2) : C₁ i≤C := by
    exact (Finset.single_le_sum (fun j _ => hC₁p j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j))))
  have hb₂ (i j : Fin 2) : C₂ i j≤C := by
    exact ((Finset.single_le_sum (fun j _ => hC₂p i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j)) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => hC₁p i)))
  refine ⟨|(2*Real.pi)⁻¹| *C,mul_nonneg (abs_nonneg _) hCp,?_⟩
  intro w hw x
  constructor
  · intro i
    rw [partial_weylRepresentative hw,abs_mul,abs_neg,← Real.norm_eq_abs]
    calc
      _ ≤ |(2*Real.pi)⁻¹| *(C*∫y,‖w y‖) := mul_le_mul_of_nonneg_left
        ((norm_rconv_le hw (smooth_partial hk i).continuous (compact_partial hc i) (fun z => (hC₁ i z).trans (hb₁ i)) x)) (abs_nonneg _)
      _ = _ := by simp only [Real.norm_eq_abs]; ring
  · intro i j
    rw [partial2_weylRepresentative hw,abs_mul,abs_neg,← Real.norm_eq_abs]
    calc
      _ ≤ |(2*Real.pi)⁻¹| *(C*∫y,‖w y‖) := mul_le_mul_of_nonneg_left
        ((norm_rconv_le hw (smooth_partial (smooth_partial hk i) j).continuous
          (compact_partial (compact_partial hc i) j) (fun z => (hC₂ i j z).trans (hb₂ i j)) x)) (abs_nonneg _)
      _ = _ := by simp only [Real.norm_eq_abs]; ring

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Decomposition
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma indicator_mul_laplacian {w ψ : Plane → ℝ} {Ω : Set Plane}
    (hsψ : tsupport ψ⊆Ω) : (fun x => Ω.indicator w x*euclideanLaplacian ψ x)=
      (fun x => w x*euclideanLaplacian ψ x) := by
  funext x
  by_cases hx : x∈Ω
  · rw [indicator_of_mem hx]
  · have hz : euclideanLaplacian ψ x=0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsψ (laplacian_tsupport_subset ψ ht)))
    simp only [hz,mul_zero]

lemma integrable_aeLogPotential_mul_compact (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {ψ : Plane → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => aeLogPotential ν x*ψ x) := by
  obtain ⟨R,hR⟩ := hcψ.isBounded.subset_ball (0:Plane)
  have hi := (aeLogPotential_integrableOn ν hs R).integrable_indicator measurableSet_ball
  apply (integrable_mul_continuous_compact hi hψ hcψ).congr
  filter_upwards [] with x
  by_cases hx : x∈Metric.ball (0:Plane) R
  · rw [indicator_of_mem hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hR ht)),mul_zero,mul_zero]

lemma potential_difference_integrable {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S) :
    Integrable ((Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)) :=
  (hw.integrableOn.sub (aeLogPotential_integrableOn ν hs 4)).integrable_indicator measurableSet_ball

lemma potential_difference_weakHarmonic {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S)
    (hrep : ∀ψ : Plane → ℝ,Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball (0:Plane) 4 →
      (∫x,w x*euclideanLaplacian ψ x)=2*Real.pi*(∫x,ψ x ∂ν)) :
    WeakHarmonicOn ((Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)) (Metric.ball (0:Plane) 4) := by
  intro ψ hψ hcψ hsψ
  rw [indicator_mul_laplacian hsψ]
  have he : (fun x => (w x-aeLogPotential ν x)*euclideanLaplacian ψ x)=
      (fun x => w x*euclideanLaplacian ψ x-aeLogPotential ν x*euclideanLaplacian ψ x) := by funext x; ring
  rw [he,integral_sub (integrable_mul_continuous_compact hw (smooth_laplacian hψ).continuous (compact_laplacian hcψ))
    (integrable_aeLogPotential_mul_compact ν hs (smooth_laplacian hψ).continuous (compact_laplacian hcψ)),
    hrep ψ hψ hcψ hsψ,aeLogPotential_distribution ν hs hψ hcψ,sub_self]

lemma potential_difference_norm_bound {w : Plane → ℝ} (hw : Integrable w)
    (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ} (hs : ∀ᵐz ∂ν,‖z‖<S) :
    (∫x,‖(Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x‖) ≤
      (∫x,‖w x‖)+ν.real univ*(∫x in Metric.ball (0:Plane) (4+S),‖Real.log ‖x‖‖) := by
  have he : (fun x => ‖(Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x‖)=
      (Metric.ball (0:Plane) 4).indicator (fun x => ‖w x-aeLogPotential ν x‖) := by
    funext x; by_cases hx : x∈Metric.ball (0:Plane) 4 <;> simp [hx]
  rw [he,integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫x in Metric.ball (0:Plane) 4,‖w x‖+‖aeLogPotential ν x‖ := integral_mono
      (hw.integrableOn.sub (aeLogPotential_integrableOn ν hs 4)).norm
      (hw.norm.integrableOn.add (aeLogPotential_integrableOn ν hs 4).norm) (fun x => norm_sub_le _ _)
    _ = (∫x in Metric.ball (0:Plane) 4,‖w x‖)+(∫x in Metric.ball (0:Plane) 4,‖aeLogPotential ν x‖) :=
      integral_add hw.norm.integrableOn (aeLogPotential_integrableOn ν hs 4).norm
    _ ≤ _ := add_le_add (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => norm_nonneg _)) hw.norm)
      (aeLogPotential_norm_bound ν hs 4)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma normalizedRiesz_finite {μ : Measure Plane} {C : ℝ}
    (hmass : μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C) :
    IsFiniteMeasure (normalizedRiesz μ) := by
  have hball : μ (Metric.ball (0:Plane) 4)≠(⊤:ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono ((Metric.ball_subset_ball (by norm_num : (4:ℝ)≤5)).trans Metric.ball_subset_closedBall)).trans hmass)
  refine ⟨?_⟩
  simp only [normalizedRiesz,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  change ENNReal.ofReal ((2*Real.pi)⁻¹)*μ (Metric.ball (0:Plane) 4)<⊤
  exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball).lt_top

lemma normalizedRiesz_support (μ : Measure Plane) : ∀ᵐz ∂normalizedRiesz μ,‖z‖<4 := by
  apply Measure.ae_smul_measure
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
  simpa only [Metric.mem_ball,dist_zero_right] using hz

lemma normalizedRiesz_mass {μ : Measure Plane} {C : ℝ} (hC : 0≤C)
    (hmass : μ (Metric.closedBall (0:Plane) 5)≤ENNReal.ofReal C) :
    (normalizedRiesz μ).real univ≤(2*Real.pi)⁻¹*C := by
  apply le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (show (normalizedRiesz μ) univ≤ENNReal.ofReal ((2*Real.pi)⁻¹)*ENNReal.ofReal C from ?_))
  · simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹),ENNReal.toReal_ofReal hC]
    exact le_rfl
  · simp only [normalizedRiesz,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact mul_le_mul' le_rfl ((measure_mono ((Metric.ball_subset_ball (by norm_num : (4:ℝ)≤5)).trans Metric.ball_subset_closedBall)).trans hmass)

lemma normalizedRiesz_test (μ : Measure Plane) {ψ : Plane → ℝ}
    (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 4) :
    2*Real.pi*(∫x,ψ x ∂normalizedRiesz μ)=∫x,ψ x ∂μ := by
  have he : (Metric.ball (0:Plane) 4).indicator ψ=ψ := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 4
    · exact indicator_of_mem hx ψ
    · rw [indicator_of_notMem hx ψ,image_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht))]
  rw [normalizedRiesz,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤(2*Real.pi)⁻¹)]
  change 2*Real.pi*((2*Real.pi)⁻¹*(∫x in Metric.ball (0:Plane) 4,ψ x ∂μ))=_
  rw [← integral_indicator measurableSet_ball,he]
  field_simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

theorem profile_ae_decomposition_uniform : ∃C : ℝ,0≤C ∧ ∀V : Plane → EReal,
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) →
    FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∃ν : Measure Plane, IsFiniteMeasure ν ∧ (∀ᵐz ∂ν,‖z‖<4) ∧ ν.real univ≤C ∧
    ∃h : Plane → ℝ,Smooth h ∧ (∀x∈Metric.ball (0:Plane) 3,euclideanLaplacian h x=0) ∧
      (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x) ∧
      (∀x : Plane,(∀i : Fin 2,|coordPartial h i x|≤C) ∧
        (∀i j : Fin 2,|coordPartial (coordPartial h i) j x|≤C)) := by
  obtain ⟨Cμ,hCμ,hμprop⟩ := profile_riesz_uniform
  obtain ⟨Ch,hCh,hderiv⟩ := uniform_weyl_derivative_bounds
  let L := ∫x in Metric.ball (0:Plane) 8,‖Real.log ‖x‖‖
  have hL : 0≤L := integral_nonneg (fun x => norm_nonneg _)
  let N := (2*Real.pi)⁻¹*Cμ
  have hN : 0≤N := by dsimp [N]; positivity
  let C := N+Ch*(100*Real.pi+N*L)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro V hV hneg htest hanchor
  obtain ⟨μ,_hμ,hmass,hrep⟩ := hμprop V hV hneg htest hanchor
  let ν := normalizedRiesz μ
  have hν : IsFiniteMeasure ν := normalizedRiesz_finite hmass
  let := hν
  have hs : ∀ᵐz ∂ν,‖z‖<4 := normalizedRiesz_support μ
  have hνmass : ν.real univ≤N := normalizedRiesz_mass hCμ hmass
  obtain ⟨a,ha,hanchor⟩ := hanchor
  have hball : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hlin := profile_lintegral_D8 hV hneg htest ha hanchor
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hball)
    (fun x hx => hneg x (hball hx)) hfin).1
  let w := (Metric.ball (0:Plane) 8).indicator (fun x => (V x).toReal)
  have hw : Integrable w := hi.integrable_indicator measurableSet_ball
  have hnorm : (∫x,‖w x‖)≤100*Real.pi := by
    have heq : (fun x => ‖w x‖)=(Metric.ball (0:Plane) 8).indicator (fun x => |(V x).toReal|) := by
      funext x
      by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx,Real.norm_eq_abs]
    rw [heq,integral_indicator measurableSet_ball]
    exact profile_norm_integral_le measurableSet_ball (hV.mono hball) (fun x hx => hneg x (hball hx)) (by positivity) hlin
  have hwrep (ψ : Plane → ℝ) (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 4) :
      (∫x,w x*euclideanLaplacian ψ x)=2*Real.pi*(∫x,ψ x ∂ν) := by
    rw [normalizedRiesz_test μ hsψ]
    rw [hrep ψ hψ hcψ (hsψ.trans (Metric.ball_subset_ball (by norm_num : (4:ℝ)≤11/2)))]
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) 8 <;> simp [w,hx]
  let d := (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x)
  have hd : Integrable d := potential_difference_integrable hw ν hs
  have hweak : WeakHarmonicOn d (Metric.ball (0:Plane) 4) := potential_difference_weakHarmonic hw ν hs hwrep
  have hdN : (∫x,‖d x‖)≤100*Real.pi+N*L := by
    exact (potential_difference_norm_bound hw ν hs).trans
      (add_le_add hnorm (by simpa only [show (4+4:ℝ)=8 by norm_num] using (mul_le_mul_of_nonneg_right hνmass hL)))
  refine ⟨ν,hν,hs,hνmass.trans (le_add_of_nonneg_right (by positivity)),
    weylRepresentative d,smooth_weylRepresentative hd,weylRepresentative_harmonic hd hweak,?_,?_⟩
  · filter_upwards [weylRepresentative_ae hd hweak] with x hx hm
    have h4 : x∈Metric.ball (0:Plane) 4 := Metric.ball_subset_ball (by norm_num : (3:ℝ)≤4) hm
    have h8 : x∈Metric.ball (0:Plane) 8 := Metric.ball_subset_ball (by norm_num : (3:ℝ)≤8) hm
    have he := hx hm
    change (Metric.ball (0:Plane) 4).indicator (fun x => w x-aeLogPotential ν x) x=weylRepresentative d x at he
    rw [indicator_of_mem h4] at he
    have hwx : w x=(V x).toReal := indicator_of_mem h8 _
    rw [hwx] at he
    linarith
  · intro x
    have hb : Ch*(∫y,‖d y‖)≤C := (mul_le_mul_of_nonneg_left hdN hCh).trans (le_add_of_nonneg_left hN)
    exact ⟨fun i => ((hderiv d hd x).1 i).trans hb,fun i j => ((hderiv d hd x).2 i j).trans hb⟩

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma profile_le_continuous_of_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hU : IsOpen U) (hUΩ : U⊆Ω)
    {g : Plane → ℝ} (hg : Continuous g)
    (hae : ∀ᵐx ∂volume.restrict U,V x≤(g x:EReal)) : ∀x∈U,V x≤(g x:EReal) := by
  intro x hx
  by_contra hh
  obtain ⟨c,hgc,hcV⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hgc' : g x < c := EReal.coe_lt_coe_iff.mp hgc
  have hne : 0≤ -V x := by simpa using EReal.neg_le_neg_iff.mpr (hneg x (hUΩ hx))
  have hnhds : U∩{y | g y < c}∈𝓝 x := (hU.inter (isOpen_lt hg continuous_const)).mem_nhds ⟨hx,hgc'⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hbU : Metric.ball x r⊆U := fun y hy => (hball hy).1
  have hlower : ENNReal.ofReal (Real.pi*r^2)*ENNReal.ofReal (-c)≤
      ∫⁻y in Metric.ball x r,(-V y).toENNReal := by
    have hb : ∀ᵐy ∂volume.restrict (Metric.ball x r),ENNReal.ofReal (-c)≤(-V y).toENNReal := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hbU hae,self_mem_ae_restrict measurableSet_ball] with y hy hym
      have hle : V y≤(c:EReal) := hy.trans (EReal.coe_le_coe_iff.mpr (hball hym).2.le)
      simpa only [← EReal.coe_neg,EReal.real_coe_toENNReal] using
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hle)
    have hi := lintegral_mono_ae hb
    simpa only [lintegral_const,Measure.restrict_apply_univ,EuclideanSpace.volume_ball_fin_two,
      ENNReal.ofReal_mul (by positivity : 0≤Real.pi),ENNReal.ofReal_pow hr.le,mul_comm] using hi
  have hu := disk_submean hV hneg htest hr (hbU.trans hUΩ)
  have hl : (-V x).toENNReal<ENNReal.ofReal (-c) := by
    simpa only [← EReal.coe_neg,EReal.real_coe_toENNReal] using
      EReal.toENNReal_lt_toENNReal hne (EReal.neg_lt_neg_iff.mpr hcV)
  apply (not_le_of_gt (ENNReal.mul_lt_mul_left (by positivity : ENNReal.ofReal (Real.pi*r^2)≠0)
    ENNReal.ofReal_ne_top hl))
  simpa only [mul_comm] using (hlower.trans hu)

lemma profile_le_continuous_of_toReal_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V Ω) (hneg : ∀x∈Ω,V x≤0)
    (htest : FullTestProperty Ω V) (hU : IsOpen U) (hUΩ : U⊆Ω)
    {g : Plane → ℝ} (hg : Continuous g)
    (hae : ∀ᵐx ∂volume.restrict U,(V x).toReal≤g x) : ∀x∈U,V x≤(g x:EReal) := by
  apply profile_le_continuous_of_ae hV hneg htest hU hUΩ hg
  filter_upwards [hae,self_mem_ae_restrict hU.measurableSet] with x hx hmem
  by_cases hb : V x=⊥
  · simp [hb]
  · have ht : V x≠⊤ := ne_top_of_le_ne_top (by simp) (hneg x (hUΩ hmem))
    rw [← EReal.coe_toReal ht hb]
    exact EReal.coe_le_coe_iff.mpr hx

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_basis_expansion (v : Plane) :
    v=(v 0) • EuclideanSpace.single 0 1+(v 1) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

lemma plane_component_norm_le (v : Plane) (i : Fin 2) : |v i|≤‖v‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

lemma plane_clm_norm_le_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Plane →L[ℝ] F) {C : ℝ} (hC : 0≤C)
    (hA : ∀i : Fin 2,‖A (EuclideanSpace.single i 1)‖≤C) : ‖A‖≤2*C := by
  apply A.opNorm_le_bound (by positivity)
  intro v
  conv_lhs => rw [plane_basis_expansion v]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(v 0) • A (EuclideanSpace.single 0 1)‖+‖(v 1) • A (EuclideanSpace.single 1 1)‖ := norm_add_le _ _
    _ = |v 0| *‖A (EuclideanSpace.single 0 1)‖+|v 1| *‖A (EuclideanSpace.single 1 1)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖v‖*C+‖v‖*C := add_le_add
      (mul_le_mul (plane_component_norm_le v 0) (hA 0) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (plane_component_norm_le v 1) (hA 1) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

lemma fderiv_norm_le_two {f : Plane → ℝ} {C : ℝ} (hC : 0≤C) (x : Plane)
    (h : ∀i : Fin 2,|coordPartial f i x|≤C) : ‖fderiv ℝ f x‖≤2*C :=
  plane_clm_norm_le_two _ hC (fun i => by simpa only [coordPartial,Real.norm_eq_abs] using h i)

lemma fderiv_sub_norm_le_two {f : Plane → ℝ} {C : ℝ} (hC : 0≤C) (x y : Plane)
    (h : ∀i : Fin 2,|coordPartial f i x-coordPartial f i y|≤C) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖≤2*C :=
  plane_clm_norm_le_two _ hC (fun i => by simpa only [sub_apply,coordPartial,Real.norm_eq_abs] using h i)

lemma affine_error_bound_ball {f : Plane → ℝ} (hf : Smooth f) {y x : Plane} {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0≤C)
    (hess : ∀z∈Metric.closedBall y r,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    (hx : x∈Metric.closedBall y r) :
    |f x-f y-(fderiv ℝ f y) (x-y)|≤4*C*r^2 := by
  have hy : y∈Metric.closedBall y r := Metric.mem_closedBall_self hr
  have hp (i : Fin 2) (z : Plane) (hz : z∈Metric.closedBall y r) :
      |coordPartial f i z-coordPartial f i y|≤2*C*r := by
    have hh := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (smooth_partial hf i).differentiable (by simp) z)
      (fun z hz => fderiv_norm_le_two hC z (hess z hz i)) hy hz
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) (by positivity))
  have hder (z : Plane) (hz : z∈Metric.closedBall y r) :
      ‖fderiv ℝ f z-fderiv ℝ f y‖≤4*C*r := by
    have ht := fderiv_sub_norm_le_two (by positivity : 0≤2*C*r) z y (fun i => hp i z hz)
    convert ht using 1 <;> first | rfl | ring
  have ht := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf.differentiable (by simp) z) hder hy hx
  rw [Real.norm_eq_abs] at ht
  exact ht.trans (by
    have hxr : ‖x-y‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    nlinarith [mul_le_mul_of_nonneg_left hxr (show 0≤4*C*r by positivity)])

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_AffineError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma fderiv_log_norm_apply {x : Plane} (hx : x≠0) (v : Plane) :
    (fderiv ℝ (fun y : Plane => Real.log ‖y‖) x) v=inner ℝ x v/‖x‖^2 := by
  have hd := (((hasFDerivAt_id (𝕜:=ℝ) x).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).const_mul (1/2:ℝ)
  have heq : (fun y : Plane => Real.log ‖y‖)=(fun y : Plane => (1/2:ℝ)*Real.log (‖y‖^2)) := by
    funext y
    rw [Real.log_pow]
    ring
  dsimp only [id_eq] at hd
  rw [heq,hd.fderiv]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply]
  ring

lemma fderiv_smoothLog_unit {w : Plane} (hw : ‖w‖=1) (v : Plane) :
    (fderiv ℝ parametrixSmoothLog w) v=inner ℝ w v := by
  have he : parametrixSmoothLog =ᶠ[𝓝 w] (fun y : Plane => Real.log ‖y‖) := by
    have hn : {y : Plane | (1/8:ℝ)<‖y‖}∈𝓝 w :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds (by norm_num [hw])
    filter_upwards [hn] with y hy
    exact parametrixSmoothLog_eq hy.le
  rw [he.fderiv_eq,fderiv_log_norm_apply (by intro h; simp [h] at hw),hw]
  norm_num

lemma smoothLog_hessian_bounded : ∃C : ℝ,0≤C ∧ ∀x∈Metric.closedBall (0:Plane) 2,
    ∀i j : Fin 2,|coordPartial (coordPartial parametrixSmoothLog i) j x|≤C := by
  let g : Plane → ℝ := fun x => ∑i : Fin 2,∑j : Fin 2,|coordPartial (coordPartial parametrixSmoothLog i) j x|
  have hg : Continuous g := continuous_finsetSum _ (fun i _ =>
    continuous_finsetSum _ (fun j _ => (smooth_partial (smooth_partial smooth_parametrixSmoothLog i) j).continuous.abs))
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Plane) 2).bddAbove_image hg.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x hx i j
  have h1 : |coordPartial (coordPartial parametrixSmoothLog i) j x|≤g x := by
    apply le_trans (Finset.single_le_sum (fun k _ => abs_nonneg (coordPartial (coordPartial parametrixSmoothLog i) k x)) (Finset.mem_univ j))
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (coordPartial (coordPartial parametrixSmoothLog k) l x))) (Finset.mem_univ i)
  exact h1.trans ((hB (mem_image_of_mem _ hx)).trans (le_max_left _ _))

lemma normalized_log_affine_error : ∃C : ℝ,0≤C ∧ ∀w v : Plane,‖w‖=1 → ‖v‖≤1/2 →
    |Real.log ‖w+v‖-inner ℝ w v|≤C*‖v‖^2 := by
  obtain ⟨C,hC,hess⟩ := smoothLog_hessian_bounded
  refine ⟨4*C,by positivity,?_⟩
  intro w v hw hv
  have hball : Metric.closedBall w ‖v‖⊆Metric.closedBall (0:Plane) 2 := by
    intro x hx
    have hn : ‖x-w‖≤‖v‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have ht := norm_add_le (x-w) w
    simp only [sub_add_cancel,hw] at ht
    simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖x‖≤2 by linarith)
  have hnorm : (1/8:ℝ)≤‖w+v‖ := by
    have ht := norm_add_le (w+v) (-v)
    simp only [add_neg_cancel_right,norm_neg,hw] at ht
    linarith
  have hh := affine_error_bound_ball smooth_parametrixSmoothLog (norm_nonneg v) hC
    (fun x hx => hess x (hball hx)) (show w+v∈Metric.closedBall w ‖v‖ by simp [dist_eq_norm])
  rw [parametrixSmoothLog_eq hnorm,parametrixSmoothLog_eq (by norm_num [hw]),hw,Real.log_one,sub_zero,
    add_sub_cancel_left,fderiv_smoothLog_unit hw] at hh
  exact hh

lemma log_far_affine_error : ∃C : ℝ,0≤C ∧ ∀x y z : Plane,∀r : ℝ,0 ≤ r →
    ‖x-y‖ ≤ r → 2*r<‖y-z‖ →
    |Real.log ‖x-z‖-Real.log ‖y-z‖-inner ℝ (y-z) (x-y)/‖y-z‖^2|≤C*r^2/‖y-z‖^2 := by
  obtain ⟨C,hC,herr⟩ := normalized_log_affine_error
  refine ⟨C,hC,?_⟩
  intro x y z r hr hxy hfar
  let d := ‖y-z‖
  have hd : 0<d := lt_of_le_of_lt (by positivity) hfar
  let w : Plane := d⁻¹ • (y-z)
  let v : Plane := d⁻¹ • (x-y)
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]; exact inv_mul_cancel₀ hd.ne'
  have hvnorm : ‖v‖=‖x-y‖/d := by simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),div_eq_mul_inv,mul_comm]
  have hv : ‖v‖≤1/2 := by rw [hvnorm,div_le_iff₀ hd]; dsimp [d]; linarith
  have hh := herr w v hw hv
  have hwv : w+v=d⁻¹ • (x-z) := by dsimp [w,v]; rw [← smul_add]; congr 1; abel
  have hxz : x-z≠0 := by
    intro he
    have he' : x=z := sub_eq_zero.mp he
    subst x
    rw [norm_sub_rev] at hxy
    linarith
  have hlog : Real.log ‖w+v‖=Real.log ‖x-z‖-Real.log d := by
    rw [hwv,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),Real.log_mul (inv_ne_zero hd.ne') (norm_ne_zero_iff.mpr hxz),Real.log_inv]
    ring
  have hinner : inner ℝ w v=inner ℝ (y-z) (x-y)/d^2 := by simp only [w,v,inner_smul_left,inner_smul_right,conj_trivial]; ring
  rw [hlog,hinner] at hh
  apply hh.trans
  rw [hvnorm]
  dsimp only [d]
  have hs : ‖x-y‖^2 ≤ r^2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
  exact (le_of_eq (by ring)).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (sq_nonneg _))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma volume_unit_disk_real : volume.real (Metric.ball (0:Plane) 1)=Real.pi := by
  simp [measureReal_def,EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_ofReal Real.pi_pos.le]

lemma log_scaled_kernel_ae {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    ∀ᵐξ : Plane, Real.log ‖y+ρ • ξ-z‖=Real.log ρ+Real.log ‖ξ-ρ⁻¹ • (z-y)‖ := by
  filter_upwards [Measure.ae_ne volume (ρ⁻¹ • (z-y))] with ξ hξ
  have he : y+ρ • ξ-z=ρ • (ξ-ρ⁻¹ • (z-y)) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hρ.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hρ,Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hξ))]

lemma log_scaled_kernel_integrable {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    IntegrableOn (fun ξ : Plane => Real.log ‖y+ρ • ξ-z‖) (Metric.ball 0 1) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  have ht : ‖ρ⁻¹ • (z-y)‖<‖ρ⁻¹ • (z-y)‖+1 := by linarith
  exact ((integrable_const (Real.log ρ)).add (log_translate_local (R:=1) ht).1).congr
    (Filter.EventuallyEq.symm (ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)))

lemma logDiskAverage_scale {ρ : ℝ} (hρ : 0<ρ) (y z : Plane) :
    logDiskAverage y ρ z=Real.log ρ+Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  have ht : ‖ρ⁻¹ • (z-y)‖<‖ρ⁻¹ • (z-y)‖+1 := by linarith
  rw [logDiskAverage,integral_congr_ae (ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)),
    integral_add (integrable_const _) (log_translate_local (R:=1) ht).1,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change Real.pi⁻¹*(volume.real (Metric.ball (0:Plane) 1)*Real.log ρ+_)=_
  rw [volume_unit_disk_real]
  field_simp

lemma log_near_average_lower {R : ℝ} (_hR : 0≤R) : ∃B : ℝ,0≤B ∧ ∀y z : Plane,∀ρ : ℝ,
    0<ρ → ‖z-y‖≤2*R*ρ → Real.log ρ-B≤logDiskAverage y ρ z := by
  let L := ∫ξ in Metric.ball (0:Plane) (2*R+2),‖Real.log ‖ξ‖‖
  refine ⟨Real.pi⁻¹*L,by positivity,?_⟩
  intro y z ρ hρ hnear
  have ht : ‖ρ⁻¹ • (z-y)‖<2*R+1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    have hle : ρ⁻¹*‖z-y‖≤2*R := by
      calc _ ≤ ρ⁻¹*(2*R*ρ) := mul_le_mul_of_nonneg_left hnear (inv_nonneg.mpr hρ.le)
           _ = _ := by field_simp
    linarith
  have hl : -(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖)≤L := by
    calc
      _ ≤ |∫ξ in Metric.ball (0:Plane) 1,Real.log ‖ξ-ρ⁻¹ • (z-y)‖| := neg_le_abs _
      _ ≤ ∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖ξ-ρ⁻¹ • (z-y)‖‖ := by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun ξ : Plane => Real.log ‖ξ-ρ⁻¹ • (z-y)‖) (μ:=volume.restrict (Metric.ball (0:Plane) 1)))
      _ ≤ L := by simpa only [show (1+(2*R+1):ℝ)=2*R+2 by ring] using (log_translate_local (R:=1) ht).2
  rw [logDiskAverage_scale hρ]
  nlinarith [mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr Real.pi_pos.le)]

lemma log_near_outer_upper {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) {x y z : Plane}
    (hx : ‖x-y‖≤R*ρ) (hz : ‖z-y‖≤2*R*ρ) (hxz : x≠z) :
    Real.log ‖x-z‖≤Real.log ρ+Real.log (3*R) := by
  have hn : ‖x-z‖≤ρ*(3*R) := by
    have htri := norm_sub_le (x-y) (z-y)
    rw [sub_sub_sub_cancel_right] at htri
    nlinarith
  have hh := Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)) hn
  rwa [Real.log_mul hρ.ne' (by positivity : (3*R:ℝ)≠0)] at hh

lemma integral_linear_unitDisk (L : Plane →L[ℝ] ℝ) :
    (∫ξ in Metric.ball (0:Plane) 1,L ξ)=0 := by
  let f := (Metric.ball (0:Plane) 1).indicator (fun ξ => L ξ)
  have he : (fun ξ => f (-ξ))=(fun ξ => -f ξ) := by
    funext ξ
    by_cases hξ : ξ∈Metric.ball (0:Plane) 1
    · have hneg : -ξ∈Metric.ball (0:Plane) 1 := by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hξ
      simp only [f,indicator_of_mem hξ,indicator_of_mem hneg,map_neg]
    · have hneg : -ξ∉Metric.ball (0:Plane) 1 := by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hξ
      simp only [f,indicator_of_notMem hξ,indicator_of_notMem hneg,neg_zero]
  have hh := integral_neg_eq_self f volume
  rw [he,integral_neg] at hh
  rw [← integral_indicator measurableSet_ball]
  change (∫ξ,f ξ)=0
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma log_far_diskAverage_error : ∃C : ℝ,0≤C ∧ ∀y z : Plane,∀ρ : ℝ,0<ρ →
    2*ρ<‖y-z‖ → |logDiskAverage y ρ z-Real.log ‖y-z‖|≤C*ρ^2/‖y-z‖^2 := by
  obtain ⟨C,hC,herr⟩ := log_far_affine_error
  refine ⟨C,hC,?_⟩
  intro y z ρ hρ hfar
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=1))⟩
  let L : Plane →L[ℝ] ℝ := (‖y-z‖^2)⁻¹ • (ρ • innerSL ℝ (y-z))
  have hL (ξ : Plane) : L ξ=inner ℝ (y-z) (ρ • ξ)/‖y-z‖^2 := by
    simp only [L,smul_apply,innerSL_apply_apply,smul_eq_mul,inner_smul_right]; ring
  let F : Plane → ℝ := fun ξ => Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖-L ξ
  have hiL : IntegrableOn (fun ξ => L ξ) (Metric.ball (0:Plane) 1) :=
    (L.continuous.continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) 1)).mono_set Metric.ball_subset_closedBall
  have hi := log_scaled_kernel_integrable hρ y z
  have hbound : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),‖F ξ‖≤C*ρ^2/‖y-z‖^2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with ξ hξ
    have hnorm : ‖y+ρ • ξ-y‖≤ρ := by
      simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      have hx : ‖ξ‖≤1 := (show ‖ξ‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using hξ).le
      nlinarith
    simpa only [F,Real.norm_eq_abs,add_sub_cancel_left,← hL] using herr (y+ρ • ξ) y z ρ hρ.le hnorm hfar
  have hh := norm_integral_le_of_norm_le_const hbound
  have hint : (∫ξ in Metric.ball (0:Plane) 1,F ξ)=Real.pi*(logDiskAverage y ρ z-Real.log ‖y-z‖) := by
    rw [show F=(fun ξ => (Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖)-L ξ) from rfl,
      integral_sub (f:=fun ξ => Real.log ‖y+ρ • ξ-z‖-Real.log ‖y-z‖) (g:=fun ξ => L ξ) (hi.sub (integrable_const (Real.log ‖y-z‖))) hiL,integral_sub hi (integrable_const (Real.log ‖y-z‖)),
      integral_linear_unitDisk,sub_zero,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
    change (∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)-volume.real (Metric.ball (0:Plane) 1)*Real.log ‖y-z‖=_
    rw [volume_unit_disk_real,logDiskAverage]
    field_simp
  rw [hint,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] at hh
  have hvol : (volume.restrict (Metric.ball (0:Plane) 1)).real univ=Real.pi := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using volume_unit_disk_real
  rw [hvol] at hh
  nlinarith [Real.pi_pos]

lemma logarithmic_kernel_comparison {R : ℝ} (hR : 1≤R) :
    ∃C : ℝ,0≤C ∧ ∀x y z : Plane,∀ρ : ℝ,0<ρ → ‖x-y‖≤R*ρ → x≠z →
    Real.log ‖x-z‖-logDiskAverage y ρ z-
      (if 2*R*ρ<‖y-z‖ then inner ℝ (y-z) (x-y)/‖y-z‖^2 else 0)
      ≤ C*(if 2*R*ρ<‖y-z‖ then ρ^2/‖y-z‖^2 else 1) := by
  obtain ⟨Cf,hCf,hfar⟩ := log_far_affine_error
  obtain ⟨Ca,hCa,hav⟩ := log_far_diskAverage_error
  obtain ⟨B,hB,hnear⟩ := log_near_average_lower (show 0≤R by linarith)
  let C := Cf*R^2+Ca+|Real.log (3*R)|+B
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x y z ρ hρ hx hxz
  split_ifs with hz
  · have hfar1 : 2*ρ<‖y-z‖ := by nlinarith
    have ho := (le_abs_self _).trans (hfar x y z (R*ρ) (by positivity) hx (by nlinarith))
    have hi := (neg_le_abs _).trans (hav y z ρ hρ hfar1)
    have hnon : 0≤ρ^2/‖y-z‖^2 := by positivity
    have hCle : Cf*R^2+Ca≤C := by dsimp [C]; linarith [abs_nonneg (Real.log (3*R))]
    have hc := mul_le_mul_of_nonneg_right hCle hnon
    nlinarith [show Cf*(R*ρ)^2/‖y-z‖^2+Ca*ρ^2/‖y-z‖^2=(Cf*R^2+Ca)*(ρ^2/‖y-z‖^2) by ring]
  · have hn : ‖z-y‖≤2*R*ρ := by rw [norm_sub_rev]; exact le_of_not_gt hz
    have ho := log_near_outer_upper (show 0<R by linarith) hρ hx hn hxz
    have hi := hnear y z ρ hρ hn
    have hlog := le_abs_self (Real.log (3*R))
    have hpos : 0≤Cf*R^2+Ca := by positivity
    dsimp [C]
    linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma scaled_log_kernel_norm_bound {ρ S : ℝ} (hρ : 0<ρ) (y z : Plane)
    (hS : ‖ρ⁻¹ • (z-y)‖<S) :
    (∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖y+ρ • ξ-z‖‖)≤
      Real.pi*|Real.log ρ|+(∫ξ in Metric.ball (0:Plane) (1+S),‖Real.log ‖ξ‖‖) := by
  have hi := (log_scaled_kernel_integrable hρ y z).norm
  have ht := (log_translate_local (R:=1) hS).1.norm
  have hle : (∫ξ in Metric.ball (0:Plane) 1,‖Real.log ‖y+ρ • ξ-z‖‖)≤
      ∫ξ in Metric.ball (0:Plane) 1,(|Real.log ρ|+‖Real.log ‖ξ-ρ⁻¹ • (z-y)‖‖) := by
    apply integral_mono_ae hi ((integrable_const _).add ht)
    filter_upwards [ae_restrict_of_ae (log_scaled_kernel_ae hρ y z)] with ξ hξ
    rw [hξ]
    simpa only [Real.norm_eq_abs,Pi.add_apply] using norm_add_le (Real.log ρ) (Real.log ‖ξ-ρ⁻¹ • (z-y)‖)
  rw [integral_add (integrable_const _) ht,integral_const] at hle
  have hvol : (volume.restrict (Metric.ball (0:Plane) 1)).real univ=Real.pi := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using volume_unit_disk_real
  rw [hvol,smul_eq_mul] at hle
  exact hle.trans (add_le_add le_rfl (log_translate_local (R:=1) hS).2)

lemma scaled_logPotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    Integrable (fun p : Plane×Plane => Real.log ‖y+ρ • p.1-p.2‖)
      ((volume.restrict (Metric.ball 0 1)).prod ν) := by
  have hm : Measurable (fun p : Plane×Plane => Real.log ‖y+ρ • p.1-p.2‖) :=
    Real.measurable_log.comp ((measurable_const.add (measurable_fst.const_smul ρ)).sub measurable_snd).norm
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun z => log_scaled_kernel_integrable hρ y z),?_⟩
  let S := ρ⁻¹*(4+‖y‖)+1
  apply (integrable_const (Real.pi*|Real.log ρ|+(∫ξ in Metric.ball (0:Plane) (1+S),‖Real.log ‖ξ‖‖))).mono'
    hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [hs] with z hz
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  apply scaled_log_kernel_norm_bound hρ y z
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
  have htri := norm_sub_le z y
  have hmul := mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr hρ.le)
  dsimp [S]
  nlinarith [inv_pos.mpr hρ]

lemma scaled_aeLogPotential_integrableOn (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    IntegrableOn (fun ξ : Plane => aeLogPotential ν (y+ρ • ξ)) (Metric.ball 0 1) :=
  (scaled_logPotential_prod_integrable ν hs hρ y).integral_prod_left

lemma logDiskAverage_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    Integrable (logDiskAverage y ρ) ν :=
  (scaled_logPotential_prod_integrable ν hs hρ y).integral_prod_right.const_mul Real.pi⁻¹

lemma integral_logDiskAverage (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {ρ : ℝ} (hρ : 0<ρ) (y : Plane) :
    (∫z,logDiskAverage y ρ z ∂ν)=Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,aeLogPotential ν (y+ρ • ξ)) := by
  rw [show logDiskAverage y ρ=(fun z => Real.pi⁻¹*(∫ξ in Metric.ball (0:Plane) 1,Real.log ‖y+ρ • ξ-z‖)) from rfl,integral_const_mul]
  have hi : Integrable (Function.uncurry (fun z ξ : Plane => Real.log ‖y+ρ • ξ-z‖))
      (ν.prod (volume.restrict (Metric.ball 0 1))) := by
    simpa only [Function.uncurry_def,Function.comp_def,Prod.fst_swap,Prod.snd_swap] using (scaled_logPotential_prod_integrable ν hs hρ y).swap
  rw [integral_integral_swap hi]
  rfl

lemma ae_source_ne (ν : Measure Plane) [IsFiniteMeasure ν] : ∀ᵐx : Plane,∀ᵐz ∂ν,x≠z := by
  apply (Measure.ae_ae_comm (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Eventually.of_forall (fun z => Measure.ae_ne volume z)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma measurable_farGradient (R ρ : ℝ) (y : Plane) : Measurable (farGradient R ρ y) := by
  exact Measurable.ite (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    ((((measurable_const.sub measurable_id).norm.pow_const 2).inv).smul (measurable_const.sub measurable_id)) measurable_const

lemma measurable_farWeight (R ρ : ℝ) (y : Plane) : Measurable (farWeight R ρ y) := by
  exact Measurable.ite (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    (measurable_const.div ((measurable_const.sub measurable_id).norm.pow_const 2)) measurable_const

lemma farGradient_inner (R ρ : ℝ) (y z v : Plane) :
    inner ℝ (farGradient R ρ y z) v=
      if 2*R*ρ<‖y-z‖ then inner ℝ (y-z) v/‖y-z‖^2 else 0 := by
  unfold farGradient
  split_ifs <;> simp only [inner_smul_left,conj_trivial,inner_zero_left]
  ring

lemma farGradient_norm_bound {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) (y z : Plane) :
    ‖farGradient R ρ y z‖≤(2*R*ρ)⁻¹ := by
  unfold farGradient
  split_ifs with hz
  · have hd : 0<‖y-z‖ := lt_trans (by positivity : 0<2*R*ρ) hz
    have he : ‖(‖y-z‖^2)⁻¹ • (y-z)‖=‖y-z‖⁻¹ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(‖y-z‖^2)⁻¹)]
      field_simp
    rw [he]
    exact (inv_le_inv₀ hd (show 0<2*R*ρ by positivity)).mpr hz.le
  · simp only [norm_zero]
    positivity

lemma farWeight_bounds {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y z : Plane) :
    0≤farWeight R ρ y z ∧ farWeight R ρ y z≤1 := by
  unfold farWeight
  split_ifs with hz
  · have hd : 0<‖y-z‖ := by nlinarith
    refine ⟨by positivity,?_⟩
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    have hsmall : ρ≤‖y-z‖ := by nlinarith
    nlinarith [sq_nonneg (‖y-z‖-ρ)]
  · exact ⟨by norm_num,le_rfl⟩

lemma integrable_farGradient (ν : Measure Plane) [IsFiniteMeasure ν]
    {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) (y : Plane) : Integrable (farGradient R ρ y) ν :=
  (integrable_const ((2*R*ρ)⁻¹)).mono' (measurable_farGradient R ρ y).aestronglyMeasurable
    (Eventually.of_forall (farGradient_norm_bound hR hρ y))

lemma integrable_farWeight (ν : Measure Plane) [IsFiniteMeasure ν]
    {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y : Plane) : Integrable (farWeight R ρ y) ν := by
  apply (integrable_const (1:ℝ)).mono' (measurable_farWeight R ρ y).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (farWeight_bounds hR hρ y z).1]
  exact (farWeight_bounds hR hρ y z).2

lemma integral_inner_left {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → Plane} (hf : Integrable f ν) (v : Plane) :
    (∫z,inner ℝ (f z) v ∂ν)=inner ℝ (∫z,f z ∂ν) v := by
  simp_rw [real_inner_comm]
  exact integral_inner hf v

lemma ae_potential_affine_comparison {R : ℝ} (hR : 1≤R) : ∃C : ℝ,0≤C ∧
    ∀ν : Measure Plane,∀[IsFiniteMeasure ν], (∀ᵐz ∂ν,‖z‖<4) →
    ∀ρ : ℝ,0<ρ → ∀y : Plane,
    ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 3), ‖x-y‖≤R*ρ →
    aeLogPotential ν x-(∫z,logDiskAverage y ρ z ∂ν)-
      inner ℝ (∫z,farGradient R ρ y z ∂ν) (x-y)≤C*(∫z,farWeight R ρ y z ∂ν) := by
  obtain ⟨C,hC,hkernel⟩ := logarithmic_kernel_comparison hR
  refine ⟨C,hC,?_⟩
  intro ν _ hs ρ hρ y
  have hg := integrable_farGradient ν (show 0<R by linarith) hρ y
  have hw := integrable_farWeight ν hR hρ y
  have ha := logDiskAverage_integrable ν hs hρ y
  filter_upwards [(logPotential_prod_integrable ν hs 3).prod_right_ae,
    ae_restrict_of_ae (ae_source_ne ν)] with x hx hne hxy
  have hi := (hx.sub ha).sub (hg.inner_const (x-y))
  have hh : (∫z,(Real.log ‖x-z‖-logDiskAverage y ρ z-inner ℝ (farGradient R ρ y z) (x-y)) ∂ν)≤
      ∫z,C*farWeight R ρ y z ∂ν := by
    apply integral_mono_ae hi (hw.const_mul C)
    filter_upwards [hne] with z hz
    simpa only [Pi.sub_apply,Pi.mul_apply,farGradient_inner,farWeight] using hkernel x y z ρ hρ hxy hz
  rw [integral_sub (f:=fun z => Real.log ‖x-z‖-logDiskAverage y ρ z) (g:=fun z => inner ℝ (farGradient R ρ y z) (x-y)) (hx.sub ha) (hg.inner_const (x-y)),
    integral_sub hx ha,integral_const_mul,integral_inner_left hg] at hh
  exact hh

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma scaled_continuous_integrable {f : Plane → ℝ} (hf : Continuous f) (y : Plane) (ρ : ℝ) :
    IntegrableOn (fun ξ : Plane => f (y+ρ • ξ)) (Metric.ball 0 1) :=
  ((hf.comp (continuous_const.add (continuous_const_smul ρ))).continuousOn.integrableOn_compact
    (isCompact_closedBall (0:Plane) 1)).mono_set Metric.ball_subset_closedBall

lemma diskAverage_linear (L : Plane →L[ℝ] ℝ) (y : Plane) (ρ : ℝ) :
    diskAverage (fun x => L (x-y)) y ρ=0 := by
  have he : (fun ξ : Plane => L (y+ρ • ξ-y))=(fun ξ => ρ * L ξ) := by
    funext ξ
    simp only [add_sub_cancel_left,map_smul,smul_eq_mul]
  simp only [diskAverage,he,integral_const_mul,integral_linear_unitDisk,mul_zero]

lemma diskAverage_const (a : ℝ) (y : Plane) (ρ : ℝ) :
    diskAverage (fun _ => a) y ρ=a := by
  simp only [diskAverage,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change Real.pi⁻¹*(volume.real (Metric.ball (0:Plane) 1)*a)=a
  rw [volume_unit_disk_real]
  field_simp

lemma diskAverage_affine_error {f : Plane → ℝ} (hf : Smooth f) {C ρ : ℝ}
    (hC : 0≤C) (hρ : 0<ρ) (hess : ∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    (y : Plane) : |diskAverage f y ρ-f y|≤4*C*ρ^2 := by
  let L := fderiv ℝ f y
  let e := fun x : Plane => f x-f y-L (x-y)
  have he : Continuous e := hf.continuous.sub continuous_const |>.sub (L.continuous.comp (continuous_id.sub continuous_const))
  have hi := scaled_continuous_integrable he y ρ
  have havg : diskAverage e y ρ=diskAverage f y ρ-f y := by
    unfold diskAverage e
    rw [integral_sub (f:=fun ξ => f (y+ρ • ξ)-f y) (g:=fun ξ => L (y+ρ • ξ-y))
      ((scaled_continuous_integrable hf.continuous y ρ).sub (integrable_const _))
      (scaled_continuous_integrable (L.continuous.comp (continuous_id.sub continuous_const)) y ρ),
      integral_sub (scaled_continuous_integrable hf.continuous y ρ) (integrable_const _)]
    have hc := diskAverage_const (f y) y ρ
    have hl := diskAverage_linear L y ρ
    dsimp [diskAverage] at hc hl
    nlinarith
  rw [← havg]
  calc
    _ = Real.pi⁻¹ * ‖∫ξ in Metric.ball (0:Plane) 1,e (y+ρ • ξ)‖ := by
      simp only [diskAverage,abs_mul,abs_of_pos (inv_pos.mpr Real.pi_pos),Real.norm_eq_abs]
    _ ≤ Real.pi⁻¹ * (∫ξ in Metric.ball (0:Plane) 1,‖e (y+ρ • ξ)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ Real.pi⁻¹ * (∫_ξ in Metric.ball (0:Plane) 1,4*C*ρ^2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
      apply integral_mono_ae hi.norm (integrable_const _)
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with ξ hξ
      have hn : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hξ
      have hx : y+ρ • ξ∈Metric.closedBall y ρ := by
        simp only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
        nlinarith
      simpa only [e,L,Real.norm_eq_abs] using affine_error_bound_ball hf hρ.le hC (fun z _ => hess z) hx
    _ = 4*C*ρ^2 := diskAverage_const _ y ρ

lemma harmonic_outer_minus_average {f : Plane → ℝ} (hf : Smooth f) {C R ρ : ℝ}
    (hC : 0≤C) (hR : 0≤R) (hρ : 0<ρ)
    (hess : ∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial f i) j z|≤C)
    {y x : Plane} (hx : ‖x-y‖≤R*ρ) :
    f x-diskAverage f y ρ-(fderiv ℝ f y) (x-y)≤4*C*(R^2+1)*ρ^2 := by
  have he := (abs_le.mp (affine_error_bound_ball hf (by positivity : 0≤R*ρ) hC
    (fun z _ => hess z) (show x∈Metric.closedBall y (R*ρ) by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx))).2
  have hav := (abs_le.mp (diskAverage_affine_error hf hC hρ hess y)).1
  nlinarith

lemma quasiMeasurePreserving_affine {ρ : ℝ} (hρ : ρ≠0) (y : Plane) :
    Measure.QuasiMeasurePreserving (fun ξ : Plane => y+ρ • ξ) volume volume :=
  (measurePreserving_add_left volume y).quasiMeasurePreserving.comp (Measure.quasiMeasurePreserving_smul volume hρ)

lemma diskAverage_le_profileSup {V : Plane → EReal} {w : Plane → ℝ} {L : Plane →L[ℝ] ℝ}
    {y : Plane} {ρ : ℝ} (hρ : 0<ρ)
    (hi : IntegrableOn (fun ξ : Plane => w (y+ρ • ξ)) (Metric.ball 0 1))
    (he : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),V (y+ρ • ξ)=(w (y+ρ • ξ):EReal)) :
    (diskAverage w y ρ:EReal)≤⨆x∈Metric.ball y ρ,V x-(L (x-y):EReal) := by
  by_contra hh
  obtain ⟨b,hsb,hba⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hba' : b<diskAverage w y ρ := EReal.coe_lt_coe_iff.mp hba
  have hpoint : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),
      w (y+ρ • ξ)-L (y+ρ • ξ-y)≤b := by
    filter_upwards [he,self_mem_ae_restrict measurableSet_ball] with ξ hξ hmem
    have hnorm : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hmem
    have hx : y+ρ • ξ∈Metric.ball y ρ := by
      simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
      nlinarith
    have hs := (le_iSup₂_of_le (y+ρ • ξ) hx le_rfl).trans_lt hsb
    rw [hξ,← EReal.coe_sub] at hs
    exact (EReal.coe_lt_coe_iff.mp hs).le
  have hlin := scaled_continuous_integrable (f:=fun x => L (x-y)) (L.continuous.comp (continuous_id.sub continuous_const)) y ρ
  have hh := integral_mono_ae (hi.sub hlin) (integrable_const b) hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi hlin] at hh
  have he' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  have hz := diskAverage_linear L y ρ
  have hb := diskAverage_const b y ρ
  dsimp [diskAverage] at hz hb
  dsimp [diskAverage] at hba'
  nlinarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_finite_ae_D3 {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) :
    ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → V x≠⊥ ∧ V x≠⊤ := by
  obtain ⟨a,ha,hVa⟩ := hanchor
  have hb : Metric.ball (0:Plane) 8⊆Metric.ball (0:Plane) 1000 := Metric.ball_subset_ball (by norm_num)
  have hi := (profile_integrable_of_lintegral_ne_top measurableSet_ball (hV.mono hb)
    (fun x hx => hneg x (hb hx))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (profile_lintegral_D8 hV hneg htest ha hVa))).2
  have hj := (ae_restrict_iff' measurableSet_ball).mp hi
  filter_upwards [hj] with x hx hm
  exact ⟨hx (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤8) hm),
    ne_top_of_le_ne_top (by simp) (hneg x (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000) hm))⟩

end SharpNodal.Profiles

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_LogGradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma norm_logGradient (x : Plane) : ‖logGradient x‖=‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,logGradient]
  · have hn := norm_pos_iff.mpr hx
    rw [logGradient,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(‖x‖^2)⁻¹)]
    field_simp

lemma measurable_logGradient : Measurable logGradient :=
  ((measurable_id.norm.pow_const 2).inv).smul measurable_id

lemma inv_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => ‖x‖⁻¹) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (α:=1) (C:=1) (by simp [Plane]) (by simp [Plane])
    _ (measurable_id.norm.inv.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.inv_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    Real.rpow_neg_one,one_mul,le_refl]

lemma inverse_translate_local {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    IntegrableOn (fun x : Plane => ‖x-z‖⁻¹) (Metric.ball 0 R) ∧
    (∫x in Metric.ball (0:Plane) R,‖x-z‖⁻¹) ≤
      ∫x in Metric.ball (0:Plane) (R+S),‖x‖⁻¹ := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator (fun x => ‖x‖⁻¹)
  have hiF : Integrable F := (inv_norm_integrableOn_ball (R+S)).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hiF.aestronglyMeasurable |>.mpr hiF
  have he : ∀x∈Metric.ball (0:Plane) R,‖x-z‖⁻¹=F (x-z) := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hnorm : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add hxR hz)
    simp only [F,indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)]
  refine ⟨hit.integrableOn.congr_fun (fun x hx => (he x hx).symm) measurableSet_ball,?_⟩
  calc
    _ = ∫x in Metric.ball (0:Plane) R,F (x-z) := setIntegral_congr_fun measurableSet_ball (fun x hx => he x hx)
    _ ≤ ∫x,F (x-z) := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => indicator_nonneg (fun x _ => inv_nonneg.mpr (norm_nonneg x)) _)) hit
    _ = ∫x,F x := integral_sub_right_eq_self F z
    _ = _ := by rw [integral_indicator measurableSet_ball]

lemma inversePotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    Integrable (fun p : Plane×Plane => ‖p.1-p.2‖⁻¹)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
  have hm : Measurable (fun p : Plane×Plane => ‖p.1-p.2‖⁻¹) :=
    ((measurable_fst.sub measurable_snd).norm).inv
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [hs] with z hz using (inverse_translate_local (R:=R) hz).1
  · apply (integrable_const (∫x in Metric.ball (0:Plane) (R+S),‖x‖⁻¹)).mono'
      hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hs] with z hz
    simp only [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (_ : Plane)))]
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => inv_nonneg.mpr (norm_nonneg _)))]
    exact (inverse_translate_local (R:=R) hz).2

lemma logGradientPotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    Integrable (fun p : Plane×Plane => logGradient (p.1-p.2))
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
  apply (inversePotential_prod_integrable ν hs R).mono'
    (measurable_logGradient.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall (fun p => (norm_logGradient _).le)

lemma aeLogGradient_integrableOn (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) : IntegrableOn (aeLogGradient ν) (Metric.ball 0 R) :=
  (logGradientPotential_prod_integrable ν hs R).integral_prod_left

lemma ae_inverse_kernel_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),
      (∀ᵐz ∂ν,x≠z) ∧ Integrable (fun z => ‖x-z‖⁻¹) ν := by
  filter_upwards [ae_restrict_of_ae (ae_source_ne ν),
    (inversePotential_prod_integrable ν hs R).prod_right_ae] with x hx hi
  exact ⟨hx,hi⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma truncated_gradient_dominating {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ)
    {x y z : Plane} (hy : ‖y-x‖≤ρ) (hz : x≠z) :
    ‖farGradient R ρ y z‖ ≤ 2*‖x-z‖⁻¹ ∧
      |farWeight R ρ y z/ρ| ≤ (2*R+2)*‖x-z‖⁻¹ := by
  have hd : 0<‖x-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have htri : ‖x-z‖≤‖y-z‖+ρ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x y z
    rw [norm_sub_rev x y] at ht
    linarith
  by_cases hf : 2*R*ρ<‖y-z‖
  · have he : 0<‖y-z‖ := by nlinarith
    have hr : ρ≤‖y-z‖ := by nlinarith
    have hgg : ‖farGradient R ρ y z‖=‖y-z‖⁻¹ := by
      rw [farGradient,ite_eq_left hf]
      exact norm_logGradient _
    have hff : farWeight R ρ y z/ρ=ρ/‖y-z‖^2 := by
      rw [farWeight,ite_eq_left hf]
      field_simp
    rw [hgg,hff,abs_of_nonneg (div_nonneg hρ.le (sq_nonneg _))]
    have hg : ‖y-z‖⁻¹≤2*‖x-z‖⁻¹ := by
      have hh : (1:ℝ)/‖y-z‖≤2/‖x-z‖ := (div_le_div_iff₀ he hd).mpr (by nlinarith)
      simpa only [one_div,div_eq_mul_inv,one_mul] using hh
    refine ⟨hg,?_⟩
    have hw : ρ/‖y-z‖^2≤‖y-z‖⁻¹ := by
      rw [div_le_iff₀ (sq_pos_of_pos he)]
      have heq : ‖y-z‖⁻¹*‖y-z‖^2=‖y-z‖ := by field_simp
      rw [heq]
      exact hr
    calc
      _ ≤ 2*‖x-z‖⁻¹ := hw.trans hg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hle := le_of_not_gt hf
    rw [farGradient,ite_eq_right hf,farWeight,ite_eq_right hf,norm_zero,one_div,
      abs_of_pos (inv_pos.mpr hρ)]
    refine ⟨by positivity,?_⟩
    have hh : (1:ℝ)/ρ≤(2*R+2)/‖x-z‖ := (div_le_div_iff₀ hρ hd).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh

lemma tendsto_truncated_kernels {R : ℝ} {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (_hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) {z : Plane} (hz : x≠z) :
    Tendsto (fun n => farGradient R (ρ n) (y n) z) atTop (𝓝 (logGradient (x-z))) ∧
    Tendsto (fun n => farWeight R (ρ n) (y n) z/ρ n) atTop (𝓝 0) := by
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n =>norm_nonneg _) hy hρlim
  have hd : ‖x-z‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  have hδlim : Tendsto (fun n => ‖y n-z‖) atTop (𝓝 ‖x-z‖) := (hylim.sub_const z).norm
  have hcut : Tendsto (fun n =>2*R*ρ n) atTop (𝓝 0) := by simpa using hρlim.const_mul (2*R)
  have hevent : ∀ᶠn in atTop,2*R*ρ n<‖y n-z‖ :=
    hcut.eventually_lt hδlim (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  refine ⟨?_,?_⟩
  · have ht := ((hδlim.pow 2).inv₀ (pow_ne_zero _ hd)).smul (hylim.sub_const z)
    apply ht.congr'
    filter_upwards [hevent] with n hn
    simp only [farGradient,ite_eq_left hn]
  · have ht : Tendsto (fun n =>ρ n/‖y n-z‖^2) atTop (𝓝 0) := by
      simpa only [Pi.div_def,zero_div] using hρlim.div (hδlim.pow 2) (pow_ne_zero _ hd)
    apply ht.congr'
    filter_upwards [hevent] with n hn
    rw [farWeight,ite_eq_left hn]
    field_simp

theorem truncated_potential_limits (ν : Measure Plane) {R : ℝ} (hR : 1≤R)
    {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) (hsep : ∀ᵐz ∂ν,x≠z)
    (hi : Integrable (fun z => ‖x-z‖⁻¹) ν) :
    Tendsto (fun n => ∫z,farGradient R (ρ n) (y n) z ∂ν) atTop (𝓝 (aeLogGradient ν x)) ∧
    Tendsto (fun n => (∫z,farWeight R (ρ n) (y n) z ∂ν)/ρ n) atTop (𝓝 0) := by
  refine ⟨?_,?_⟩
  · apply tendsto_integral_of_dominated_convergence (fun z =>2*‖x-z‖⁻¹)
      (fun n =>(measurable_farGradient R (ρ n) (y n)).aestronglyMeasurable) (hi.const_mul 2)
    · intro n
      filter_upwards [hsep] with z hz using (truncated_gradient_dominating hR (hρ n) (hy n) hz).1
    · filter_upwards [hsep] with z hz using (tendsto_truncated_kernels hρ hρlim hy hz).1
  · have ht := tendsto_integral_of_dominated_convergence (μ:=ν) (f:=fun _ : Plane =>(0:ℝ))
      (fun z =>(2*R+2)*‖x-z‖⁻¹)
      (fun n =>((measurable_farWeight R (ρ n) (y n)).div_const (ρ n)).aestronglyMeasurable)
      (hi.const_mul (2*R+2)) (fun n =>?_) ?_
    · simpa only [integral_div,integral_zero] using ht
    · filter_upwards [hsep] with z hz using (by simpa only [Real.norm_eq_abs] using
        (truncated_gradient_dominating hR (hρ n) (hy n) hz).2)
    · filter_upwards [hsep] with z hz using (tendsto_truncated_kernels hρ hρlim hy hz).2

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma partial_regularizedLog_bound {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    ‖coordPartial (regularizedLog ε) i x‖ ≤ ‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,partial_regularizedLog hε]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  rw [partial_regularizedLog hε,norm_div,Real.norm_of_nonneg (logDenom_pos hε x).le]
  apply (div_le_iff₀ (logDenom_pos hε x)).mpr
  calc
    ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    _ = ‖x‖⁻¹*‖x‖^2 := by field_simp
    _ ≤ ‖x‖⁻¹*logDenom ε x := mul_le_mul_of_nonneg_left (by dsimp [logDenom]; nlinarith [sq_nonneg ε]) (by positivity)

lemma partial_regularizedLog_tendsto (i : Fin 2) {x : Plane} (hx : x≠0) :
    Tendsto (fun ε : ℝ => coordPartial (regularizedLog ε) i x) (𝓝[>]0)
      (𝓝 (logGradient x i)) := by
  have hn : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have ht : Tendsto (fun ε : ℝ => x i/(‖x‖^2+ε^2)) (𝓝[>]0) (𝓝 (x i/‖x‖^2)) := by
    apply Tendsto.div tendsto_const_nhds _ hn
    simpa using ((tendsto_const_nhds (x:=‖x‖^2)).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).pow 2)).mono_left nhdsWithin_le_nhds
  have he : x i/‖x‖^2=logGradient x i := by simp [logGradient,div_eq_mul_inv,mul_comm]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (partial_regularizedLog hε i x).symm

lemma partial_regularizedLog_test_limit (i : Fin 2) {g : Plane → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun ε : ℝ => ∫x,coordPartial (regularizedLog ε) i x*g x) (𝓝[>]0)
      (𝓝 (∫x,logGradient x i*g x)) := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  let B := fun x : Plane => ‖x‖⁻¹*M
  have hiB : IntegrableOn B (Metric.ball 0 R) := (inv_norm_integrableOn_ball R).mul_const M
  have hne : ∀ᵐx : Plane,x≠0 := by simp [ae_iff]
  have ht := tendsto_integral_filter_of_dominated_convergence (l:=𝓝[>] (0:ℝ)) B
    (F:=fun ε x =>coordPartial (regularizedLog ε) i x*g x)
    (f:=fun x =>logGradient x i*g x)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using
      ((smooth_partial (smooth_regularizedLog hε) i).continuous.mul hg).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul (partial_regularizedLog_bound hε i x) (hM (mem_range_self x))
        (norm_nonneg _) (by positivity)) hiB
    (by filter_upwards [ae_restrict_of_ae hne] with x hx using
      (partial_regularizedLog_tendsto i hx).mul_const (g x))
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  simpa only [he] using ht

lemma logarithmic_gradient_distribution {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫x,Real.log ‖x‖*coordPartial ψ i x)= -(∫x,logGradient x i*ψ x) := by
  have hl := regularizedLog_test_limit (smooth_partial hψ i).continuous (compact_partial hcψ i)
  have hr := (partial_regularizedLog_test_limit i hψ.continuous hcψ).neg
  have he : (fun ε : ℝ => ∫x,regularizedLog ε x*coordPartial ψ i x)=ᶠ[𝓝[>]0]
      (fun ε => -(∫x,coordPartial (regularizedLog ε) i x*ψ x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_mul_partial (smooth_regularizedLog hε) hψ hcψ i
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma logarithmic_gradient_distribution_translate {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) (z : Plane) :
    (∫x,Real.log ‖x-z‖*coordPartial ψ i x)= -(∫x,logGradient (x-z) i*ψ x) := by
  rw [← integral_add_right_eq_self (fun x => Real.log ‖x-z‖*coordPartial ψ i x) z,
    ← integral_add_right_eq_self (fun x => logGradient (x-z) i*ψ x) z]
  simp only [add_sub_cancel_right]
  have hs : Smooth (fun x => ψ (x+z)) := hψ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun x => ψ (x+z)) := hcψ.comp_homeomorph (Homeomorph.addRight z)
  simpa only [partial_translate hψ] using logarithmic_gradient_distribution hs hc i

lemma aeLogGradient_component_test_swap (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (i : Fin 2) :
    (∫x,aeLogGradient ν x i*g x) = ∫z,(∫x,logGradient (x-z) i*g x) ∂ν := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  have hp := logGradientPotential_prod_integrable ν hs R
  have hi : Integrable (fun p : Plane×Plane => logGradient (p.1-p.2) i)
      ((volume.restrict (Metric.ball 0 R)).prod ν) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integrable_comp hp
  have hint : Integrable (fun p : Plane×Plane => logGradient (p.1-p.2) i*g p.1)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
    apply (hi.norm.mul_const M).mono'
      (hi.aestronglyMeasurable.mul (hg.measurable.comp measurable_fst).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖logGradient (p.1-p.2) i*g p.1‖≤‖logGradient (p.1-p.2) i‖*M
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM (mem_range_self p.1)) (norm_nonneg _)
  rw [← he (fun x =>aeLogGradient ν x i)]
  calc
    _ = ∫x in Metric.ball (0:Plane) R,∫z,logGradient (x-z) i*g x ∂ν := by
      apply integral_congr_ae
      filter_upwards [hp.prod_right_ae] with x hx
      rw [integral_mul_const]
      have hc := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integral_comp_comm hx
      exact congrArg (fun t : ℝ => t*g x) hc.symm
    _ = ∫z,(∫x in Metric.ball (0:Plane) R,logGradient (x-z) i*g x) ∂ν := integral_integral_swap hint
    _ = _ := by simp only [he]

lemma aeLogPotential_gradient_distribution (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    (i : Fin 2) :
    (∫x,aeLogPotential ν x*coordPartial ψ i x)= -(∫x,aeLogGradient ν x i*ψ x) := by
  rw [aeLogPotential_test_swap ν hs (smooth_partial hψ i).continuous (compact_partial hcψ i),
    aeLogGradient_component_test_swap ν hs hψ.continuous hcψ i]
  simp only [logarithmic_gradient_distribution_translate hψ hcψ,integral_neg]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma weakGradient_rconv_partial {w : Plane → ℝ} (hw : Integrable w) {R : ℝ}
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R))
    (φ : ContDiffBump (0:Plane)) {z : Plane} (hz : ‖z‖+φ.rOut<R) (i : Fin 2) :
    coordPartial (rconv w (φ.normed volume)) i z=0 := by
  have hφ : Smooth (φ.normed volume) := φ.contDiff_normed
  have hcφ := φ.hasCompactSupport_normed (μ:=volume)
  let ψ : Plane → ℝ := fun x =>φ.normed volume (z-x)
  have hψ : Smooth ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.subLeft z)
  have hsψ : tsupport ψ⊆Metric.ball (0:Plane) R := by
    apply closure_minimal _ Metric.isClosed_closedBall |>.trans
      (Metric.closedBall_subset_ball (show ‖z‖+φ.rOut<R from hz))
    intro x hx
    have hx' : z-x∈Function.support (φ.normed volume) := hx
    rw [φ.support_normed_eq] at hx'
    have hd : ‖z-x‖<φ.rOut := by simpa only [Metric.mem_ball,dist_zero_right] using hx'
    have hn := norm_sub_norm_le z x
    simp only [Metric.mem_closedBall,dist_zero_right]
    have ht := norm_sub_le z (z-x)
    simp only [sub_sub_cancel] at ht
    linarith
  have hh := hzero ψ hψ hcψ hsψ i
  have hp : coordPartial ψ i=(fun x => -coordPartial (φ.normed volume) i (z-x)) :=
    funext (fun x =>partial_reflection hφ z x i)
  rw [hp] at hh
  simp only [mul_neg,integral_neg,neg_eq_zero] at hh
  rw [partial_rconv hw hφ hcφ,rconv_eq]
  exact hh

lemma weakGradient_rconv_constant {w : Plane → ℝ} (hw : Integrable w) {R r : ℝ}
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R))
    (φ : ContDiffBump (0:Plane)) (hr : r+φ.rOut≤R)
    {x y : Plane} (hx : x∈Metric.ball (0:Plane) r) (hy : y∈Metric.ball (0:Plane) r) :
    rconv w (φ.normed volume) x=rconv w (φ.normed volume) y := by
  have hs := smooth_rconv hw (φ.contDiff_normed (μ:=volume)) φ.hasCompactSupport_normed
  apply Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0:Plane) r).isPreconnected
    (hs.differentiable (by simp)).differentiableOn _ hx hy
  intro z hz
  apply norm_le_zero_iff.mp
  have hz' : ‖z‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have hh := fderiv_norm_le_two (f:=rconv w (φ.normed volume)) (C:=0) le_rfl z
    (fun i =>by rw [weakGradient_rconv_partial hw hzero φ (by linarith) i,abs_zero])
  simpa only [mul_zero] using hh

lemma gradientBump_tendsto : Tendsto (fun n => (gradientBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma rconv_normed_eq (w : Plane → ℝ) (φ : ContDiffBump (0:Plane)) (x : Plane) :
    rconv w (φ.normed volume) x=
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] w) x := by
  rw [rconv_swap,convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul,mul_comm]

lemma ae_gradientBump_converges {w : Plane → ℝ} (hw : Integrable w) :
    ∀ᵐx : Plane,Tendsto (fun n => rconv w ((gradientBump n).normed volume) x) atTop (𝓝 (w x)) := by
  have hratio : ∀ᶠn : ℕ in atTop,(gradientBump n).rOut≤2*(gradientBump n).rIn := by
    filter_upwards [] with n
    change 1/((n:ℝ)+1)≤2*(1/(2*((n:ℝ)+1)))
    have hn : (n:ℝ)+1≠0 := by positivity
    field_simp
    norm_num
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ:=volume) gradientBump_tendsto hratio hw.locallyIntegrable
  simpa only [rconv_normed_eq] using hh

theorem weakGradient_constant_ae {w : Plane → ℝ} (hw : Integrable w) {R : ℝ} (hR : 0<R)
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R)) :
    ∃c : ℝ,∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),w x=c := by
  have hlim := ae_gradientBump_converges hw
  obtain ⟨a,ha,halim⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (μ:=volume) (s:=Metric.ball (0:Plane) R)
    (Metric.measure_ball_pos volume (0:Plane) hR).ne' (ae_restrict_of_ae hlim)
  refine ⟨w a,?_⟩
  filter_upwards [ae_restrict_of_ae hlim,self_mem_ae_restrict measurableSet_ball] with x hxlim hx
  have haR : ‖a‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  obtain ⟨r,hlo,hhi⟩ := exists_between (max_lt haR hxR)
  have he : (fun n =>rconv w ((gradientBump n).normed volume) x)=ᶠ[atTop]
      (fun n =>rconv w ((gradientBump n).normed volume) a) := by
    filter_upwards [gradientBump_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr hhi))] with n hn
    exact weakGradient_rconv_constant (r:=r) hw hzero (gradientBump n) (by linarith)
      (by simpa only [Metric.mem_ball,dist_zero_right] using (le_max_right ‖a‖ ‖x‖).trans_lt hlo)
      (by simpa only [Metric.mem_ball,dist_zero_right] using (le_max_left ‖a‖ ‖x‖).trans_lt hlo)
  exact tendsto_nhds_unique hxlim (halim.congr' he.symm)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma aeLogGradient_locallyIntegrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) : LocallyIntegrable (aeLogGradient ν) volume := by
  intro x
  exact ⟨Metric.ball (0:Plane) (‖x‖+1),Metric.isOpen_ball.mem_nhds (by
    simp only [Metric.mem_ball,dist_zero_right]; linarith),aeLogGradient_integrableOn ν hs _⟩

lemma potential_sum_gradient_distribution (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {h ψ : Plane → ℝ} (hh : Smooth h) (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫x,(h x+aeLogPotential ν x)*coordPartial ψ i x)=
      -(∫x,(coordPartial h i x+aeLogGradient ν x i)*ψ x) := by
  have hip := integrable_aeLogPotential_mul_compact ν hs (smooth_partial hψ i).continuous (compact_partial hcψ i)
  have hg : LocallyIntegrable (fun x =>aeLogGradient ν x i) volume := by
    intro x
    obtain ⟨u,hu,hi⟩ := aeLogGradient_locallyIntegrable ν hs x
    exact ⟨u,hu,(EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integrable_comp hi⟩
  have hig : Integrable (fun x =>aeLogGradient ν x i*ψ x) := by
    exact hg.integrable_smul_right_of_hasCompactSupport hψ.continuous hcψ
  simp_rw [add_mul]
  rw [integral_add (integrable_mul_compact_right hh (smooth_partial hψ i) (compact_partial hcψ i)) hip,
    integral_add (integrable_mul_compact_right (smooth_partial hh i) hψ hcψ) hig,
    integral_mul_partial hh hψ hcψ i,aeLogPotential_gradient_distribution ν hs hψ hcψ i]
  ring

lemma potential_zeroGradient_weak (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {h : Plane → ℝ} (hh : Smooth h)
    (he : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),
      fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)=0) :
    WeakGradientZeroOn ((Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x))
      (Metric.ball (0:Plane) 2) := by
  intro ψ hψ hcψ hsψ i
  have hsP : tsupport (coordPartial ψ i)⊆Metric.ball (0:Plane) 2 := (partial_tsupport_subset _ _).trans hsψ
  have hcut : (fun x =>((Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x) x)*coordPartial ψ i x)=
      (fun x =>(h x+aeLogPotential ν x)*coordPartial ψ i x) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 3
    · rw [indicator_of_mem hx]
    · have hz : coordPartial ψ i x=0 := image_eq_zero_of_notMem_tsupport (fun ht =>
        hx (Metric.ball_subset_ball (by norm_num : (2:ℝ)≤3) (hsP ht)))
      simp only [hz,mul_zero]
  rw [hcut,potential_sum_gradient_distribution ν hs hh hψ hcψ i,neg_eq_zero]
  apply integral_eq_zero_of_ae
  have hea := (ae_restrict_iff' measurableSet_ball).mp he
  filter_upwards [hea] with x hx
  by_cases hm : x∈Metric.ball (0:Plane) 2
  · have hi := congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (hx hm)
    have hi' : coordPartial h i x+aeLogGradient ν x i=0 := by
      simpa only [add_apply,zero_apply,innerSL_apply_apply,
        EuclideanSpace.inner_single_right,coordPartial,starRingEnd_apply,star_trivial,one_mul] using hi
    simp only [hi',zero_mul,Pi.zero_apply]
  · simp only [image_eq_zero_of_notMem_tsupport (fun ht =>hm (hsψ ht)),mul_zero,Pi.zero_apply]

lemma profile_eq_constant_of_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Ω,V x≤0) (htest : FullTestProperty Ω V)
    (hU : IsOpen U) (hUΩ : U⊆Ω) {c : ℝ}
    (he : ∀ᵐx ∂volume.restrict U,V x=(c:EReal)) : ∀x∈U,V x=(c:EReal) := by
  have hupper := profile_le_continuous_of_ae (hV.upperSemicontinuousOn _) hneg htest hU hUΩ
    (g:=fun _ =>c) continuous_const (he.mono (fun _ hx =>hx.le))
  have hle : ∀ᵐx ∂volume.restrict U,(c:EReal)≤V x := he.mono (fun _ hx =>hx.ge)
  have hnull : volume (U∩V ⁻¹' Iio (c:EReal))=0 := by
    have hh := ae_imp_of_ae_restrict hle
    simpa only [ae_iff,Classical.not_imp,not_le,Set.inter_def,Set.preimage,Set.mem_Iio,Set.mem_ofPred_eq] using hh
  have hempty := (hU.inter (hV.isOpen_preimage (c:EReal))).eq_empty_of_measure_zero hnull
  intro x hx
  refine le_antisymm (hupper x hx) ?_
  by_contra hn
  have hm : x∈U∩V ⁻¹' Iio (c:EReal) := ⟨hx,lt_of_not_ge hn⟩
  rw [hempty] at hm
  exact hm

theorem profile_nonzero_gradient (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {V : Plane → EReal} {h : Plane → ℝ}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    (hh : Smooth h) (hrep : ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x)
    (hnonconstant : ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y) :
    ∃x∈Metric.ball (0:Plane) 2,(∀ᵐz ∂ν,x≠z) ∧ Integrable (fun z =>‖x-z‖⁻¹) ν ∧
      fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)≠0 := by
  by_contra hno
  have hzero : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)=0 := by
    filter_upwards [ae_inverse_kernel_integrable ν hs 2,self_mem_ae_restrict measurableSet_ball] with x hx hm
    by_contra hn
    exact hno ⟨x,hm,hx.1,hx.2,hn⟩
  let w := (Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x)
  have hw : Integrable w := by
    apply IntegrableOn.integrable_indicator _ measurableSet_ball
    exact (hh.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0:Plane) 3)).mono_set Metric.ball_subset_closedBall
      |>.add (aeLogPotential_integrableOn ν hs 3)
  obtain ⟨c,hc⟩ := weakGradient_constant_ae hw (by norm_num : (0:ℝ)<2) (potential_zeroGradient_weak ν hs hh hzero)
  have hcast : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),V x=(c:EReal) := by
    filter_upwards [hc,ae_restrict_of_ae hrep,
      ae_restrict_of_ae (profile_finite_ae_D3 (hV.upperSemicontinuousOn _) hneg htest hanchor),
      self_mem_ae_restrict measurableSet_ball] with x hcx hrep hf hm
    have h3 := Metric.ball_subset_ball (by norm_num : (2:ℝ)≤3) hm
    rw [← EReal.coe_toReal (hf h3).2 (hf h3).1,hrep h3]
    have hwx : w x=h x+aeLogPotential ν x := indicator_of_mem h3 _
    rw [← hwx,hcx]
  have hall := profile_eq_constant_of_ae hV hneg htest Metric.isOpen_ball
    (Metric.ball_subset_ball (by norm_num : (2:ℝ)≤1000)) hcast
  obtain ⟨x,hx,y,hy,hne⟩ := hnonconstant
  exact hne ((hall x hx).trans (hall y hy).symm)

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Persistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman
theorem local_potential_profile_affine_sup_bound {R : ℝ} (hR : 1≤R) : ∃Ck : ℝ,0≤Ck ∧
    ∀(ν : Measure Plane) [IsFiniteMeasure ν], (∀ᵐz ∂ν,‖z‖<4) →
    ∀(V : Plane → EReal) (h : Plane → ℝ),
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) → FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    Smooth h →
    (∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x) →
    ∀Ch : ℝ,0≤Ch → (∀z : Plane,∀i j : Fin 2,|coordPartial (coordPartial h i) j z|≤Ch) →
    ∀ρ : ℝ,0<ρ → ∀y : Plane,‖y‖+2*R*ρ<3 →
    let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
    let e : ℝ := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
    (⨆x∈Metric.closedBall y (R*ρ),V x-(L (x-y):EReal))≤
      (⨆x∈Metric.ball y ρ,V x-(L (x-y):EReal))+(e:EReal) := by
  obtain ⟨Ck,hCk,hpot⟩ := ae_potential_affine_comparison (show 1≤2*R by linarith)
  refine ⟨Ck,hCk,?_⟩
  intro ν _ hs V h hV hneg htest hanchor hh heq Ch hCh hhess ρ hρ y hsmall
  dsimp only
  let L := fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*R) ρ y z ∂ν)
  let a := diskAverage h y ρ+∫z,logDiskAverage y ρ z ∂ν
  let e := 4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν)
  let U := Metric.ball y (2*R*ρ)
  have hRpos : 0<R := by linarith
  have hU3 : U⊆Metric.ball (0:Plane) 3 := by
    intro x hx
    have hx' : ‖x-y‖<2*R*ρ := by simpa only [U,Metric.mem_ball,dist_eq_norm] using hx
    have hn := norm_add_le (x-y) y
    rw [sub_add_cancel] at hn
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  have hUΩ := hU3.trans (Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000))
  have hupper : ∀x∈U,V x≤((a+L (x-y)+e:ℝ):EReal) := by
    apply profile_le_continuous_of_toReal_ae hV hneg htest Metric.isOpen_ball hUΩ
      ((continuous_const.add (L.continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hU3 (hpot ν hs ρ hρ y),
      ae_restrict_of_ae heq,self_mem_ae_restrict measurableSet_ball] with x hpx hex hmem
    have hx : ‖x-y‖≤(2*R)*ρ := (show ‖x-y‖<2*R*ρ by simpa only [U,Metric.mem_ball,dist_eq_norm] using hmem).le
    have hp := hpx hx
    have hh' := harmonic_outer_minus_average hh hCh (show 0≤2*R by positivity) hρ hhess hx
    rw [hex (hU3 hmem)]
    dsimp [a,L,e]
    change h x+aeLogPotential ν x≤diskAverage h y ρ+(∫z,logDiskAverage y ρ z ∂ν)+
      ((fderiv ℝ h y) (x-y)+inner ℝ (∫z,farGradient (2*R) ρ y z ∂ν) (x-y))+
      (4*Ch*((2*R)^2+1)*ρ^2+Ck*(∫z,farWeight (2*R) ρ y z ∂ν))
    linarith
  let w := fun x => h x+aeLogPotential ν x
  have hwi : IntegrableOn (fun ξ : Plane => w (y+ρ • ξ)) (Metric.ball 0 1) :=
    (scaled_continuous_integrable hh.continuous y ρ).add (scaled_aeLogPotential_integrableOn ν hs hρ y)
  have hfinite := profile_finite_ae_D3 hV hneg htest hanchor
  have hwV : ∀ᵐξ ∂volume.restrict (Metric.ball (0:Plane) 1),V (y+ρ • ξ)=(w (y+ρ • ξ):EReal) := by
    filter_upwards [ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae heq),
      ae_restrict_of_ae ((quasiMeasurePreserving_affine hρ.ne' y).ae hfinite),
      self_mem_ae_restrict measurableSet_ball] with ξ hξ hfξ hmem
    have hnorm : ‖ξ‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hmem
    have h3 : y+ρ • ξ∈Metric.ball (0:Plane) 3 := by
      have hm := norm_add_le y (ρ • ξ)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hm
      simp only [Metric.mem_ball,dist_zero_right]
      nlinarith
    rw [← EReal.coe_toReal (hfξ h3).2 (hfξ h3).1,hξ h3]
  have hav : diskAverage w y ρ=a := by
    dsimp [diskAverage,w,a]
    rw [integral_add (scaled_continuous_integrable hh.continuous y ρ) (scaled_aeLogPotential_integrableOn ν hs hρ y),
      integral_logDiskAverage ν hs hρ y]
    ring
  have hinner := diskAverage_le_profileSup (L:=L) hρ hwi hwV
  rw [hav] at hinner
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hxU : x∈U := by
    have hx' : ‖x-y‖≤R*ρ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    simp only [U,Metric.mem_ball,dist_eq_norm]
    nlinarith
  have hhx : V x-(L (x-y):EReal)≤((a+e:ℝ):EReal) := by
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
    simpa only [← EReal.coe_add,add_assoc,add_comm,add_left_comm] using hupper x hxU
  exact hhx.trans (by simpa only [L,e,EReal.coe_add] using add_le_add hinner (le_refl (e:EReal)))

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace SharpNodal.Profiles

lemma exists_extendedGridCenter {r : ℝ} (hr : 0 < r) (x : Plane) :
    ∃p : Fin 2 → ℤ,‖extendedGridCenter r p-x‖ ≤ r := by
  let p : Fin 2 → ℤ := fun i => ⌊(x i+1/2)/r⌋
  refine ⟨p,?_⟩
  have hd (i : Fin 2) : |(extendedGridCenter r p-x) i| ≤ r/2 := by
    have hl := Int.floor_le ((x i+1/2)/r)
    have hu := Int.lt_floor_add_one ((x i+1/2)/r)
    have hl' := (le_div_iff₀ hr).mp hl
    have hu' := (div_lt_iff₀ hr).mp hu
    change |-1/2+((p i:ℝ)+1/2)*r-x i| ≤ r/2
    change (p i:ℝ)*r≤x i+1/2 at hl'
    change x i+1/2<((p i:ℝ)+1)*r at hu'
    rw [abs_le]
    constructor <;> nlinarith
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hd 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hd 1) 2
  rw [sq_abs] at h0 h1
  have hn := EuclideanSpace.real_norm_sq_eq (extendedGridCenter r p-x)
  rw [Fin.sum_univ_two] at hn
  nlinarith [norm_nonneg (extendedGridCenter r p-x)]

lemma tendsto_gridScale {A : ℕ} (hA : 1<A) :
    Tendsto (fun m : ℕ => ((A:ℝ)⁻¹)^m) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · positivity
  · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hA)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma potential_affine_coefficient_limits (ν : Measure Plane) {R Ch Ck : ℝ} (hR : 1≤R)
    {h : Plane → ℝ} (hh : Smooth h) {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) (hsep : ∀ᵐz ∂ν,x≠z)
    (hi : Integrable (fun z => ‖x-z‖⁻¹) ν) :
    Tendsto (fun n =>fderiv ℝ h (y n)+innerSL ℝ (∫z,farGradient (2*R) (ρ n) (y n) z ∂ν))
      atTop (𝓝 (fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x))) ∧
    Tendsto (fun n => (4*Ch*((2*R)^2+1)*(ρ n)^2+Ck*(∫z,farWeight (2*R) (ρ n) (y n) z ∂ν))/ρ n)
      atTop (𝓝 0) := by
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n =>norm_nonneg _) hy hρlim
  obtain ⟨hg,he⟩ := truncated_potential_limits ν (by linarith : 1≤2*R) hρ hρlim hy hsep hi
  refine ⟨?_,?_⟩
  · exact ((hh.continuous_fderiv (by simp)).tendsto x |>.comp hylim).add
      ((innerSL ℝ).continuous.tendsto _ |>.comp hg)
  · have ht := (hρlim.const_mul (4*Ch*((2*R)^2+1))).add (he.const_mul Ck)
    have heq : (fun n =>4*Ch*((2*R)^2+1)*ρ n+Ck*((∫z,farWeight (2*R) (ρ n) (y n) z ∂ν)/ρ n))=
        (fun n =>(4*Ch*((2*R)^2+1)*(ρ n)^2+Ck*(∫z,farWeight (2*R) (ρ n) (y n) z ∂ν))/ρ n) := by
      funext n
      field_simp
    simpa only [zero_mul,mul_zero,add_zero,heq] using ht

theorem profile_small_affine_grid_gap_oai {A : ℕ} (hA : 1<A) {R σ : ℝ} (hR : 1≤R) (hσ : 0<σ)
    {V : Plane → EReal} (hV : UpperSemicontinuous V)
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    (hnonconstant : ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y)
    (m₀ : ℕ) :
    ∃m≥m₀,∃p : Fin 2 → ℤ,∃c : Plane,∃e : ℝ,
      let r := ((A:ℝ)⁻¹)^m
      let y := extendedGridCenter r p
      0<‖c‖ ∧ ‖y‖+2*R*r<3 ∧ R*r<1/4 ∧ e<σ*r*‖c‖ ∧
      (⨆x∈Metric.closedBall y (R*r),V x-(inner ℝ c (x-y):EReal))≤
        (⨆x∈Metric.ball y r,V x-(inner ℝ c (x-y):EReal))+(e:EReal) := by
  obtain ⟨Ch,hCh,hdec⟩ := profile_ae_decomposition_uniform
  obtain ⟨ν,hν,hs,_hm,h,hh,_hharm,hrep,hder⟩ := hdec V (hV.upperSemicontinuousOn _) hneg htest hanchor
  let := hν
  obtain ⟨x,hx,hsep,hi,hnz⟩ := profile_nonzero_gradient ν hs hV hneg htest hanchor hh hrep hnonconstant
  let ρ : ℕ → ℝ := fun m =>((A:ℝ)⁻¹)^m
  have hρ (m : ℕ) : 0<ρ m := by dsimp [ρ]; positivity
  have hρlim : Tendsto ρ atTop (𝓝 0) := tendsto_gridScale hA
  choose p hp using fun m =>exists_extendedGridCenter (hρ m) x
  let y : ℕ → Plane := fun m =>extendedGridCenter (ρ m) (p m)
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m =>norm_nonneg _) hp hρlim
  obtain ⟨Ck,_hCk,hbound⟩ := local_potential_profile_affine_sup_bound hR
  let L := fun m =>fderiv ℝ h (y m)+innerSL ℝ (∫z,farGradient (2*R) (ρ m) (y m) z ∂ν)
  let e := fun m =>4*Ch*((2*R)^2+1)*(ρ m)^2+Ck*(∫z,farWeight (2*R) (ρ m) (y m) z ∂ν)
  let L₀ := fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)
  have hL₀ : 0<‖L₀‖ := norm_pos_iff.mpr hnz
  obtain ⟨hL,he⟩ := potential_affine_coefficient_limits (Ch:=Ch) (Ck:=Ck) ν hR hh hρ hρlim hp hsep hi
  have hnonzero : ∀ᶠm in atTop,0<‖L m‖ := hL.norm.eventually (lt_mem_nhds hL₀)
  have hgap : ∀ᶠm in atTop,e m/ρ m<σ*‖L m‖ := he.eventually_lt (hL.norm.const_mul σ) (mul_pos hσ hL₀)
  have hsmall : ∀ᶠm in atTop,‖y m‖+2*R*ρ m<3 := by
    have ht : Tendsto (fun m =>‖y m‖+2*R*ρ m) atTop (𝓝 ‖x‖) := by
      simpa only [mul_zero,add_zero] using hylim.norm.add (hρlim.const_mul (2*R))
    apply ht.eventually (gt_mem_nhds _)
    have hx' : ‖x‖<2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    linarith
  have hmargin : ∀ᶠm in atTop,R*ρ m<1/4 := by
    have ht : Tendsto (fun m =>R*ρ m) atTop (𝓝 0) := by simpa using hρlim.const_mul R
    exact ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))
  obtain ⟨m,hm,hn,he',hs',hr'⟩ := ((eventually_ge_atTop m₀).and (hnonzero.and (hgap.and (hsmall.and hmargin)))).exists
  let c := (toDual ℝ Plane).symm (L m)
  have hc (v : Plane) : inner ℝ c v=L m v :=
    congrArg (fun f : Plane →L[ℝ] ℝ =>f v) ((toDual ℝ Plane).apply_symm_apply (L m))
  have hcn : ‖c‖=‖L m‖ := (toDual ℝ Plane).symm.norm_map _
  refine ⟨m,hm,p m,c,e m,?_,hs',hr',?_,?_⟩
  · rwa [hcn]
  · change e m<σ*ρ m*‖c‖
    rw [hcn]
    have ht := (div_lt_iff₀ (hρ m)).mp he'
    nlinarith
  · simpa only [hc] using hbound ν hs V h (hV.upperSemicontinuousOn _) hneg htest hanchor hh hrep Ch hCh
      (fun z i j =>(hder z).2 i j) (ρ m) (hρ m) (y m) hs'

end SharpNodal.Profiles
end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.profile_small_affine_grid_gap_oai := @OAI.SharpNodal.Profiles.profile_small_affine_grid_gap_oai
