-- Prove2me | solution 1 for OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:00:11.860743+00:00
-- url     : https://prove2.me/submissions/a957e6c1-ceee-456c-bb1b-57dc435ab43e

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_zero_curvature
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_zero_curvature_local_normal

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem closed_flat_set_contains_plane {S : Set Cover} (hS : IsClosed S)
    {N : Cover → Cover} (hN : Continuous N)
    (hloc : ∀ a∈S,∀ᶠ v in 𝓝 (0 : Cover),
      (a+v∈S ↔ ⟪N a,v⟫=0) ∧ (a+v∈S → N (a+v)=N a))
    {a : Cover} (ha : a∈S) (b : Cover) (hb : ⟪N a,b-a⟫=0) :
    b∈S ∧ N b=N a := by
  let P : Set Cover := {x | ⟪N a,x⟫=⟪N a,a⟫}
  have hPc : Convex ℝ P :=
    (convex_singleton (⟪N a,a⟫ : ℝ)).linear_preimage (innerSL ℝ (N a)).toLinearMap
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hPc.isPreconnected
  let T : Set P := {x | (x : Cover)∈S ∧ N x=N a}
  have hTc : IsClosed T := (hS.preimage continuous_subtype_val).inter
    (isClosed_eq (hN.comp continuous_subtype_val) continuous_const)
  have hTo : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have ht : Tendsto (fun y : P ↦ (y : Cover)-(x : Cover)) (𝓝 x) (𝓝 (0 : Cover)) := by
      have hc : Continuous (fun y : P ↦ (y : Cover)-(x : Cover)) := continuous_subtype_val.sub continuous_const
      simpa only [sub_self] using hc.tendsto x
    filter_upwards [ht.eventually (hloc x hx.1)] with y hy
    have hv : ⟪N x,(y : Cover)-(x : Cover)⟫=0 := by
      rw [hx.2,inner_sub_right]
      exact sub_eq_zero.mpr (y.property.trans x.property.symm)
    have hadd : (x : Cover)+((y : Cover)-(x : Cover))=(y : Cover) := by abel
    have hys := hy.1.mpr hv
    change (y : Cover)∈S ∧ N y=N a
    have hyN : N (y : Cover)=N (x : Cover) := by simpa only [hadd] using hy.2 hys
    exact ⟨by simpa only [hadd] using hys,hyN.trans hx.2⟩
  have hTu : T=univ := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ ⟨⟨a,rfl⟩,ha,rfl⟩
  have hbp : b∈P := by
    change ⟪N a,b⟫=⟪N a,a⟫
    rw [inner_sub_right,sub_eq_zero] at hb
    exact hb
  have hmem : (⟨b,hbp⟩ : P)∈T := by rw [hTu]; trivial
  exact hmem

namespace Periodic

theorem isMinimizerAt_connected_or_complete_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ᶠ v in 𝓝 (0 : Cover),
            (quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪N a,v⟫=0) ∧
            (quotientMap (a+v)∈frontier (openRepresentative E) → N (a+v)=N a)) ∧
        ∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hb,hs,hcf⟩ :=
    isMinimizerAt_connected_or_zero_curvature hV hE hmin
  rcases hcf with hc|hq
  · exact Or.inl hc
  · have hloc := isMinimizerAt_zero_curvature_local_normal hV hE hmin hμ hN hp hae
      (fun x hx ↦ (hb x hx).1) hq
    refine Or.inr ⟨N,hN,hp,fun a ha ↦ (hloc a ha).1,fun a ha ↦ (hloc a ha).2,?_⟩
    intro a ha b hb
    exact closed_flat_set_contains_plane (isClosed_frontier.preimage continuous_quotientMap)
      hN.continuous (fun a ha ↦ (hloc a ha).2) ha b hb

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_LatticeHeightHom
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem complete_planes_normals_parallel {S : Set Cover} {N : Cover → Cover}
    (hunit : ∀ x∈S,‖N x‖=1)
    (hplane : ∀ a∈S,∀ b,⟪N a,b-a⟫=0 → b∈S ∧ N b=N a)
    {a b : Cover} (ha : a∈S) (hb : b∈S) : N b=N a ∨ N b= -N a := by
  let n := N a
  let m := N b
  let d := ⟪n,m⟫
  have hn : ‖n‖=1 := hunit a ha
  have hm : ‖m‖=1 := hunit b hb
  have hd : d^2=1 := by
    by_contra hd
    have hden : 1-d^2≠0 := sub_ne_zero.mpr (Ne.symm hd)
    let A := ⟪n,a⟫
    let B := ⟪m,b⟫
    let c := ((A-d*B)/(1-d^2)) • n+((B-d*A)/(1-d^2)) • m
    have hcn : ⟪n,c⟫=A := by
      simp only [c,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
      change (A-d*B)/(1-d^2)+(B-d*A)/(1-d^2)*d=A
      field_simp
      ring
    have hcm : ⟪m,c⟫=B := by
      rw [show c=((A-d*B)/(1-d^2)) • n+((B-d*A)/(1-d^2)) • m from rfl,
        inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hm,
        one_pow,mul_one,real_inner_comm n m]
      change (A-d*B)/(1-d^2)*d+(B-d*A)/(1-d^2)=B
      field_simp
      ring
    have hca := hplane a ha c (by change ⟪n,c-a⟫=0; rw [inner_sub_right,hcn]; exact sub_self _)
    have hcb := hplane b hb c (by change ⟪m,c-b⟫=0; rw [inner_sub_right,hcm]; exact sub_self _)
    have hnm : n=m := hca.2.symm.trans hcb.2
    have hd1 : d=1 := by
      dsimp only [d]
      rw [hnm,real_inner_self_eq_norm_sq,hm,one_pow]
    exact hd (by rw [hd1,one_pow])
  have hdor : d=1 ∨ d= -1 := by
    have he : (d-1)*(d+1)=0 := by nlinarith
    rcases mul_eq_zero.mp he with h|h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hdor with hd1|hd1
  · left
    change m=n
    have hs : ‖m-n‖^2=0 := by
      rw [norm_sub_sq_real,hm,hn,real_inner_comm n m]
      change 1^2-2*d+1^2=0
      rw [hd1]; norm_num
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  · right
    change m= -n
    have hs : ‖m+n‖^2=0 := by
      rw [norm_add_sq_real,hm,hn,real_inner_comm n m]
      change 1^2+2*d+1^2=0
      rw [hd1]; norm_num
    have he : m+n=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    exact eq_neg_iff_add_eq_zero.mpr he

namespace Periodic

theorem isMinimizerAt_connected_or_parallel_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ᶠ v in 𝓝 (0 : Cover),
            (quotientMap (a+v)∈frontier (openRepresentative E) ↔ ⟪N a,v⟫=0) ∧
            (quotientMap (a+v)∈frontier (openRepresentative E) → N (a+v)=N a)) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a) ∧
        ∀ a b,quotientMap a∈frontier (openRepresentative E) →
          quotientMap b∈frontier (openRepresentative E) → N b=N a ∨ N b= -N a := by
  rcases isMinimizerAt_connected_or_complete_planes hV hE hmin with hc|⟨N,hN,hp,hu,hloc,hplane⟩
  · exact Or.inl hc
  · exact Or.inr ⟨N,hN,hp,hu,hloc,hplane,fun a b ha hb ↦
      complete_planes_normals_parallel hu hplane ha hb⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem flat_periodic_normal_integral {S : Set Cover} {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hS : ∀ m x,x∈S → x+latticeVector m∈S)
    (hunit : ∀ x∈S,‖N x‖=1)
    (hplane : ∀ a∈S,∀ b,⟪N a,b-a⟫=0 → b∈S ∧ N b=N a)
    (hloc : ∀ a∈S,∀ᶠ v in 𝓝 (0 : Cover),a+v∈S ↔ ⟪N a,v⟫=0)
    {a : Cover} (ha : a∈S) :
    ∃ (c : ℝ) (m : Fin 3 → ℤ),c≠0 ∧ m≠0 ∧ N a=c • latticeVector m ∧
      (latticeHeightHom (N a)).range=AddSubgroup.zmultiples c := by
  let n := N a
  have hn : ‖n‖=1 := hunit a ha
  obtain ⟨r,hr,hrloc⟩ := Metric.mem_nhds_iff.mp (hloc a ha)
  have hgap : Disjoint (↑(latticeHeightHom n).range : Set ℝ) (Ioo 0 r) := by
    apply Set.disjoint_left.mpr
    rintro t ⟨k,rfl⟩ ht
    let t := ⟪n,latticeVector k⟫
    change 0<t ∧ t < r at ht
    have hkt : a+t • n∈S := by
      apply (hplane (a+latticeVector k) (hS k a ha) (a+t • n) ?_).1
      rw [hp]
      change ⟪n,(a+t • n)-(a+latticeVector k)⟫=0
      rw [show (a+t • n)-(a+latticeVector k)=t • n-latticeVector k by abel,
        inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn]
      change t*1^2-t=0
      ring
    have hsmall : t • n∈Metric.ball (0 : Cover) r := by
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,hn,mul_one,
        abs_of_pos ht.1]
      exact ht.2
    have he := (hrloc hsmall).mp hkt
    change ⟪n,t • n⟫=0 at he
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at he
    exact (ne_of_gt ht.1) he
  obtain ⟨c,hc⟩ := AddSubgroup.cyclic_of_isolated_zero hr hgap
  have hc' : (latticeHeightHom n).range=AddSubgroup.zmultiples c := by
    rw [AddSubgroup.zmultiples_eq_closure]
    exact hc
  have hcoords (i : Fin 3) : ∃ z : ℤ,(z : ℝ)*c=n i := by
    have hi : n i∈(latticeHeightHom n).range := by
      refine ⟨Pi.single i 1,?_⟩
      change ⟪n,latticeVector (Pi.single i 1)⟫=n i
      have hv : latticeVector (Pi.single i 1)=EuclideanSpace.single i 1 := by
        ext j
        simp [latticeVector,Pi.single_apply]
      rw [hv,EuclideanSpace.inner_single_right]
      simp
    rw [hc',AddSubgroup.mem_zmultiples_iff] at hi
    simpa only [zsmul_eq_mul] using hi
  choose m hm using hcoords
  have hnm : n=c • latticeVector m := by
    ext i
    change n i=c*(m i : ℝ)
    rw [← hm i,mul_comm]
  have hc0 : c≠0 := by
    intro hz
    have he : n=0 := by rw [hnm,hz,zero_smul]
    rw [he,norm_zero] at hn
    norm_num at hn
  have hm0 : m≠0 := by
    intro hz
    have he : n=0 := by rw [hnm,hz,latticeVector_zero,smul_zero]
    rw [he,norm_zero] at hn
    norm_num at hn
  exact ⟨c,m,hc0,hm0,hnm,hc'⟩

namespace Periodic

theorem isMinimizerAt_connected_or_integral_planes {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
        (∀ m x,N (x+latticeVector m)=N x) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) → ‖N a‖=1) ∧
        (∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∀ b,⟪N a,b-a⟫=0 → quotientMap b∈frontier (openRepresentative E) ∧ N b=N a) ∧
        (∀ a b,quotientMap a∈frontier (openRepresentative E) →
          quotientMap b∈frontier (openRepresentative E) → N b=N a ∨ N b= -N a) ∧
        ∀ a,quotientMap a∈frontier (openRepresentative E) →
          ∃ (c : ℝ) (m : Fin 3 → ℤ),c≠0 ∧ m≠0 ∧ N a=c • latticeVector m ∧
            (latticeHeightHom (N a)).range=AddSubgroup.zmultiples c := by
  rcases isMinimizerAt_connected_or_parallel_planes hV hE hmin with hc|⟨N,hN,hp,hu,hloc,hplane,hpar⟩
  · exact Or.inl hc
  · refine Or.inr ⟨N,hN,hp,hu,hplane,hpar,?_⟩
    intro a ha
    apply flat_periodic_normal_integral hp (S := quotientMap ⁻¹' frontier (openRepresentative E))
      ?_ hu hplane (fun a ha ↦ (hloc a ha).mono fun v hv ↦ hv.1) ha
    intro m x hx
    change quotientMap (x+latticeVector m)∈frontier (openRepresentative E)
    rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    exact hx

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem continuous_line_avoids_frontier {U : Set Torus} (hU : IsOpen U)
    {f : ℝ → Torus} (hf : Continuous f) (havoid : ∀ t,f t∉frontier U)
    (s t : ℝ) : f s∈U ↔ f t∈U := by
  have he : f ⁻¹' closure U=f ⁻¹' U := by
    ext r
    constructor
    · intro hr
      by_contra hn
      exact havoid r (by rw [hU.frontier_eq]; exact ⟨hr,hn⟩)
    · intro hr
      exact subset_closure hr
  have hc : IsClopen (f ⁻¹' U) := ⟨by rw [← he]; exact isClosed_closure.preimage hf,
    hU.preimage hf⟩
  constructor
  · intro hs
    have hu := hc.eq_univ ⟨s,hs⟩
    change t∈f ⁻¹' U
    rw [hu]
    exact mem_univ t
  · intro ht
    have hu := hc.eq_univ ⟨t,ht⟩
    change s∈f ⁻¹' U
    rw [hu]
    exact mem_univ s

theorem open_phase_tangent_invariant {U : Set Torus} (hU : IsOpen U)
    {n : Cover}
    (hplane : ∀ a,quotientMap a∈frontier U → ∀ b,⟪n,b-a⟫=0 →
      quotientMap b∈frontier U)
    {x y : Cover} (hxy : ⟪n,y-x⟫=0) : quotientMap x∈U ↔ quotientMap y∈U := by
  by_cases hx : quotientMap x∈frontier U
  · have hy := hplane x hx y hxy
    have hx' : quotientMap x∉U := by rw [hU.frontier_eq] at hx; exact hx.2
    have hy' : quotientMap y∉U := by rw [hU.frontier_eq] at hy; exact hy.2
    exact iff_of_false hx' hy'
  · let f : ℝ → Torus := fun t ↦ quotientMap (x+t • (y-x))
    have hf : Continuous f := continuous_quotientMap.comp
      (continuous_const.add (continuous_id.smul continuous_const))
    have ha (t : ℝ) : f t∉frontier U := by
      intro ht
      apply hx
      apply hplane (x+t • (y-x)) ht x
      rw [show x-(x+t • (y-x))= -(t • (y-x)) by abel,
        inner_neg_right,real_inner_smul_right,hxy,mul_zero,neg_zero]
    simpa only [f,zero_smul,add_zero,one_smul,add_sub_cancel] using
      continuous_line_avoids_frontier hU hf ha 0 1

theorem open_planar_phase_factor {U : Set Torus} (hU : IsOpen U)
    {n : Cover} (hn : ‖n‖=1)
    (hplane : ∀ a,quotientMap a∈frontier U → ∀ b,⟪n,b-a⟫=0 →
      quotientMap b∈frontier U)
    {c : ℝ} (hc : c∈(latticeHeightHom n).range) :
    ∃ J : Set ℝ,IsOpen J ∧ (∀ t,t+c∈J ↔ t∈J) ∧
      ∀ x,quotientMap x∈U ↔ ⟪n,x⟫∈J := by
  let J : Set ℝ := (fun t : ℝ ↦ quotientMap (t • n)) ⁻¹' U
  have hJ : IsOpen J := hU.preimage (continuous_quotientMap.comp
    (continuous_id.smul continuous_const))
  have hfactor (x : Cover) : quotientMap x∈U ↔ ⟪n,x⟫∈J := by
    apply open_phase_tangent_invariant hU hplane
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn]
    ring
  refine ⟨J,hJ,?_,hfactor⟩
  obtain ⟨k,hk⟩ := hc
  change ⟪n,latticeVector k⟫=c at hk
  intro t
  have hx : ⟪n,t • n⟫=t := by
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  have hy : ⟪n,t • n+latticeVector k⟫=t+c := by rw [inner_add_right,hx,hk]
  rw [← hy,← hfactor,quotientMap_add,quotientMap_latticeVector,add_zero,hfactor,hx]

namespace Periodic

theorem isMinimizerAt_connected_or_planar_phase {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (n : Cover) (c : ℝ) (m : Fin 3 → ℤ) (J : Set ℝ),
        ‖n‖=1 ∧ c≠0 ∧ m≠0 ∧ n=c • latticeVector m ∧
        (latticeHeightHom n).range=AddSubgroup.zmultiples c ∧
        IsOpen J ∧ (∀ t,t+c∈J ↔ t∈J) ∧
        ∀ x,quotientMap x∈openRepresentative E ↔ ⟪n,x⟫∈J := by
  classical
  by_cases hconn : IsPreconnected (frontier (openRepresentative E))
  · exact Or.inl hconn
  obtain ⟨N,hN,hp,hu,hplane,hpar,hint⟩ :=
    (isMinimizerAt_connected_or_integral_planes hV hE hmin).resolve_left hconn
  have hnon : (frontier (openRepresentative E)).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    exact hconn (he.symm ▸ isPreconnected_empty)
  obtain ⟨z,hz⟩ := hnon
  let a := representative z
  have ha : quotientMap a∈frontier (openRepresentative E) := by
    simpa only [a,quotientMap_representative] using hz
  obtain ⟨c,m,hc,hm,hnm,hcyc⟩ := hint a ha
  have hfixed (b : Cover) (hb : quotientMap b∈frontier (openRepresentative E))
      (d : Cover) (hd : ⟪N a,d-b⟫=0) : quotientMap d∈frontier (openRepresentative E) := by
    apply (hplane b hb d ?_).1
    rcases hpar a b ha hb with h|h
    · rwa [h]
    · rw [h,inner_neg_left,hd,neg_zero]
  have hc' : c∈(latticeHeightHom (N a)).range := by
    rw [hcyc]
    exact AddSubgroup.mem_zmultiples c
  obtain ⟨J,hJ,hperiod,hfactor⟩ := open_planar_phase_factor (isOpen_openRepresentative E)
    (hu a ha) hfixed hc'
  exact Or.inr ⟨N a,c,m,J,hu a ha,hc,hm,hnm,hcyc,hJ,hperiod,hfactor⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_integerCharacter (m : Fin 3 → ℤ) : Continuous (integerCharacter m) := by
  change Continuous (fun x : Torus ↦ ∑ i,m i • x i)
  exact continuous_finsetSum Finset.univ fun i _ ↦
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ)) i).zsmul (m i)

lemma integerCharacter_quotientMap (m : Fin 3 → ℤ) (x : Cover) :
    integerCharacter m (quotientMap x)=(⟪latticeVector m,x⟫ : AddCircle (1 : ℝ)) := by
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=_
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,latticeVector,WithLp.ofLp_toLp]
  change (∑ i,m i • (x i : AddCircle (1 : ℝ)))=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (∑ i,x i*(m i : ℝ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,← zsmul_eq_mul]
  rfl

lemma integerCharacter_surjective {m : Fin 3 → ℤ} (hm : m≠0) :
    Function.Surjective (integerCharacter m) := by
  have hi : ∃ i,m i≠0 := by
    by_contra hn
    push Not at hn
    exact hm (funext hn)
  obtain ⟨i,hi⟩ := hi
  intro z
  let t : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z).1
  refine ⟨quotientMap (EuclideanSpace.single i (t/(m i : ℝ))),?_⟩
  rw [integerCharacter_quotientMap,EuclideanSpace.inner_single_right]
  simp only [latticeVector,WithLp.ofLp_toLp,starRingEnd_apply,star_trivial]
  rw [div_mul_cancel₀ t (by exact_mod_cast hi)]
  exact AddCircle.coe_equivIco

theorem integerCharacter_measurePreserving {m : Fin 3 → ℤ} (hm : m≠0) :
    MeasurePreserving (integerCharacter m) torusVolume volume := by
  have hc := continuous_integerCharacter m
  let : (Measure.map (integerCharacter m) torusVolume).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure torusVolume (integerCharacter m) hc
      (integerCharacter_surjective hm)
  let : IsProbabilityMeasure (Measure.map (integerCharacter m) torusVolume) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  refine ⟨hc.measurable,?_⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_open_phase_descends {L : Set ℝ} (hL : IsOpen L)
    (hp : ∀ t,t+1∈L ↔ t∈L) :
    ∃ K : Set (AddCircle (1 : ℝ)),IsOpen K ∧ ∀ t : ℝ,(t : AddCircle (1 : ℝ))∈K ↔ t∈L := by
  have hper : Function.Periodic (fun t ↦ t∈L) 1 := fun t ↦ propext (hp t)
  let K : Set (AddCircle (1 : ℝ)) := hper.lift
  have he : K=(fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' L := by
    ext z
    obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
    constructor
    · intro h
      exact ⟨t,h,rfl⟩
    · rintro ⟨s,hs,he⟩
      change hper.lift (t : AddCircle (1 : ℝ))
      rw [← he]
      exact hs
  refine ⟨K,?_,fun _ ↦ Iff.rfl⟩
  rw [he]
  exact QuotientAddGroup.isOpenMap_coe _ hL

theorem Periodic.isMinimizerAt_connected_or_circle_phase_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    IsPreconnected (frontier (openRepresentative E)) ∨
      ∃ (m : Fin 3 → ℤ) (K : Set (AddCircle (1 : ℝ))),m≠0 ∧ IsOpen K ∧
        openRepresentative E=(integerCharacter m) ⁻¹' K ∧
        volume K=ENNReal.ofReal V := by
  rcases Periodic.isMinimizerAt_connected_or_planar_phase hV hE hmin with hconn|
    ⟨n,c,m,J,hn,hc,hm,hnm,hcyc,hJ,hperiod,hfactor⟩
  · exact Or.inl hconn
  let L : Set ℝ := (fun t : ℝ ↦ c*t) ⁻¹' J
  have hL : IsOpen L := hJ.preimage (continuous_const.mul continuous_id)
  have hLP (t : ℝ) : t+1∈L ↔ t∈L := by
    change c*(t+1)∈J ↔ c*t∈J
    simpa only [mul_add,mul_one] using hperiod (c*t)
  obtain ⟨K,hK,hKL⟩ := periodic_open_phase_descends hL hLP
  have hfactorK (x : Cover) : quotientMap x∈openRepresentative E ↔
      integerCharacter m (quotientMap x)∈K := by
    rw [integerCharacter_quotientMap,hKL]
    change quotientMap x∈openRepresentative E ↔ c*⟪latticeVector m,x⟫∈J
    rw [← real_inner_smul_left,← hnm]
    exact hfactor x
  have he : openRepresentative E=(integerCharacter m) ⁻¹' K := by
    ext z
    simpa only [quotientMap_representative,Set.mem_preimage] using hfactorK (representative z)
  refine Or.inr ⟨m,K,hm,hK,he,?_⟩
  rw [← (integerCharacter_measurePreserving hm).measure_preimage hK.measurableSet.nullMeasurableSet,
    ← he]
  exact (measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmin)).trans hmin.2.1

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase_oai := @OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase_oai
