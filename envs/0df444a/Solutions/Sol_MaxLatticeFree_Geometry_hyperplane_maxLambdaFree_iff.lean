-- Prove2me | solution 1 for MaxLatticeFree.Geometry.hyperplane_maxLambdaFree_iff
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:15:57.036173+00:00
-- url     : https://prove2.me/submissions/33454d27-a42d-43ec-b4e6-0f7fd1235a22

-- Adapted from the external accepted theorem9 proof, submission
-- fe37f171-6a7a-45e8-b259-ee963587c72a. Relevant helper blocks are reproduced
-- in full below; provenance and original bytes are preserved under source/.
-- Licensed under Apache 2.0, as in the accepted source.
import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree

open Pointwise

-- Begin NativeInterior

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma intW_subtype_iff (U S : Set (EuclideanSpace ℝ (Fin n))) (x : U) :
    (x : EuclideanSpace ℝ (Fin n)) ∈ intW U S ↔
      x ∈ interior ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' S) := by
  constructor
  · rintro ⟨_,ε,hε,hball⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply Metric.mem_nhds_iff.mpr
    refine ⟨ε,hε,?_⟩
    intro y hy
    exact hball ⟨hy,y.property⟩
  · intro hx
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    have hxS : x ∈ (Subtype.val : U → _) ⁻¹' S := interior_subset hx
    refine ⟨hxS,ε,hε,?_⟩
    rintro y ⟨hy,hyU⟩
    exact hball (show (⟨y,hyU⟩ : U) ∈ Metric.ball x ε from hy)

lemma intW_eq_subtype_image (U S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ U) :
    intW U S = Subtype.val '' interior ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨x,hS hx.1⟩,(intW_subtype_iff U S _).mp hx,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact (intW_subtype_iff U S y).mpr hy

lemma relint_eq_intrinsicInterior (S : Set (EuclideanSpace ℝ (Fin n))) :
    relint S = intrinsicInterior ℝ S := by
  exact intW_eq_subtype_image _ S (subset_affineSpan ℝ S)

end MaxLatticeFree.Geometry.Proof
-- End NativeInterior

-- Begin GenericFree

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Interior lattice-freeness in the space currently under consideration. -/
def Free (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Convex ℝ S ∧ ∀ x ∈ interior S, x ∉ Γ

/-- Maximality among convex sets free of the specified additive subgroup. -/
def MaxFree (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Free Γ S ∧ ∀ K : Set E, Free Γ K → S ⊆ K → K = S

end MaxLatticeFree.Geometry.Proof
-- End GenericFree

-- Begin NativeFree

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma nativeFree_iff (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : S ⊆ (W : Set (EuclideanSpace ℝ (Fin n)))) :
    IsLambdaFree Λ W S ↔
      Free (Λ.comap W.subtype.toAddMonoidHom) ((Subtype.val : W → _) ⁻¹' S) := by
  constructor
  · rintro ⟨_,hconv,hfree⟩
    refine ⟨hconv.linear_preimage W.subtype,?_⟩
    intro x hx hxΛ
    have hnative := (intW_subtype_iff (W : Set _) S x).mpr hx
    have hh : (x : EuclideanSpace ℝ (Fin n)) ∈ (Λ : Set _) ∩ intW (W : Set _) S := ⟨hxΛ,hnative⟩
    rw [hfree] at hh
    exact hh
  · rintro ⟨hconv,hfree⟩
    refine ⟨hS,?_,?_⟩
    · have he : Subtype.val '' ((Subtype.val : W → _) ⁻¹' S)=S := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩; exact hy
        · intro hx; exact ⟨⟨x,hS hx⟩,hx,rfl⟩
      rw [← he]
      exact hconv.linear_image W.subtype
    · apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxΛ,hxint⟩
      let y : W := ⟨x,hS hxint.1⟩
      exact hfree y ((intW_subtype_iff (W : Set _) S y).mp hxint) hxΛ

lemma nativeMaxFree_iff (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : S ⊆ (W : Set (EuclideanSpace ℝ (Fin n)))) :
    IsMaxLambdaFree Λ W S ↔
      MaxFree (Λ.comap W.subtype.toAddMonoidHom) ((Subtype.val : W → _) ⁻¹' S) := by
  constructor
  · rintro ⟨hfree,hmax⟩
    refine ⟨(nativeFree_iff Λ W S hS).mp hfree,?_⟩
    intro K hK hSK
    let T : Set (EuclideanSpace ℝ (Fin n)) := Subtype.val '' K
    have hTW : T ⊆ (W : Set _) := by rintro _ ⟨x,_,rfl⟩; exact x.property
    have hpre : (Subtype.val : W → _) ⁻¹' T=K :=
      Set.preimage_image_eq K Subtype.val_injective
    have hT : IsLambdaFree Λ W T := (nativeFree_iff Λ W T hTW).mpr (hpre.symm ▸ hK)
    have hST : S ⊆ T := fun x hx => ⟨⟨x,hS hx⟩,hSK hx,rfl⟩
    have he := hmax T hT hST
    rw [← hpre,he]
  · rintro ⟨hfree,hmax⟩
    refine ⟨(nativeFree_iff Λ W S hS).mpr hfree,?_⟩
    intro K hK hSK
    have hpre := hmax ((Subtype.val : W → _) ⁻¹' K)
      ((nativeFree_iff Λ W K hK.1).mp hK) (preimage_mono hSK)
    apply Subset.antisymm ?_ hSK
    intro x hx
    have hy : (⟨x,hK.1 hx⟩ : W) ∈ (Subtype.val : W → _) ⁻¹' K := hx
    rw [hpre] at hy
    exact hy

end MaxLatticeFree.Geometry.Proof
-- End NativeFree

-- Begin ScalarSubgroupGap

open Set
namespace MaxLatticeFree.Geometry.Proof

lemma nondense_real_group_step (H:AddSubgroup ℝ) (h : ¬Dense (H:Set ℝ)) :
    ∃p:ℝ,0<p ∧ ∀x∈H,∃z:ℤ,x=(z:ℝ)*p := by
  obtain ⟨a,ha⟩ := H.dense_or_cyclic.resolve_left h
  by_cases hz : a=0
  · refine ⟨1,zero_lt_one,?_⟩
    intro x hx
    rw [ha,hz] at hx
    have hx0 : x=0 := by
      rw [AddSubgroup.mem_closure_singleton] at hx
      obtain ⟨z,rfl⟩ := hx
      simp
    exact ⟨0,by simp [hx0]⟩
  · refine ⟨|a|,abs_pos.mpr hz,?_⟩
    intro x hx
    rw [ha,AddSubgroup.mem_closure_singleton] at hx
    obtain ⟨z,rfl⟩ := hx
    by_cases hp : 0≤a
    · exact ⟨z,by simp [abs_of_nonneg hp,zsmul_eq_mul]⟩
    · exact ⟨-z,by simp [abs_of_neg (lt_of_not_ge hp),zsmul_eq_mul]⟩

lemma nondense_real_group_slab (H:AddSubgroup ℝ) (h : ¬Dense (H:Set ℝ)) (b:ℝ) :
    ∃l u:ℝ,l<u ∧ b∈Icc l u ∧ ∀x∈H,x∉Ioo l u := by
  obtain ⟨p,hp,hstep⟩ := nondense_real_group_step H h
  let m : ℤ := ⌊b/p⌋
  refine ⟨(m:ℝ)*p,((m:ℝ)+1)*p,by nlinarith,?_,?_⟩
  · constructor
    · have hh := Int.floor_le (b/p)
      have he : (b/p)*p=b := div_mul_cancel₀ b hp.ne'
      dsimp [m]
      nlinarith [mul_le_mul_of_nonneg_right hh hp.le]
    · have hh := Int.lt_floor_add_one (b/p)
      have he : (b/p)*p=b := div_mul_cancel₀ b hp.ne'
      dsimp [m]
      nlinarith [mul_lt_mul_of_pos_right hh hp]
  · intro x hx hh
    obtain ⟨z,rfl⟩ := hstep x hx
    have h1r : (m:ℝ) < z := by nlinarith [hh.1]
    have h1 : m < z := by exact_mod_cast h1r
    have h2r : (z:ℝ) < (m:ℝ) + 1 := by nlinarith [hh.2]
    have h2 : z < m + 1 := by exact_mod_cast h2r
    omega

end MaxLatticeFree.Geometry.Proof
-- End ScalarSubgroupGap

-- Begin HyperplaneGeometry

open Set Metric
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma functional_unit (f : E →L[ℝ] ℝ) (hf : f≠0) : ∃e:E,f e=1 := by
  have hx : ∃x:E,f x≠0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext h)
  obtain ⟨x,hx⟩ := hx
  exact ⟨(f x)⁻¹ • x,by simp [hx]⟩

lemma hyperplane_interior (f : E →L[ℝ] ℝ) (hf : f≠0) (b:ℝ) :
    interior {x:E | f x=b}=∅ := by
  obtain ⟨e,he⟩ := functional_unit f hf
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let t := ε/(2*(‖e‖+1))
  have ht : 0<t := by dsimp [t]; positivity
  have htn : t*‖e‖<ε := by
    have heq : t*(2*(‖e‖+1))=ε := by dsimp [t]; field_simp
    nlinarith [norm_nonneg e]
  have hx' : x∈{x:E | f x=b} := interior_subset hx
  change f x=b at hx'
  have hy' : x+t • e∈interior {x:E | f x=b} := hball (by
    simpa [mem_ball,dist_eq_norm,norm_smul,abs_of_pos ht] using htn)
  have hy : x+t • e∈{x:E | f x=b} := interior_subset hy'
  change f (x+t • e)=b at hy
  simp only [map_add,map_smul,he,smul_eq_mul,mul_one,hx'] at hy
  linarith

lemma slab_subset_convex (f : E →L[ℝ] ℝ) (b:ℝ) {K:Set E} (hK:Convex ℝ K)
    (hP : {x:E | f x=b}⊆K) {w:E} (hw:w∈K) (hb:b<f w) :
    {z:E | b<f z ∧ f z<f w}⊆K := by
  intro z hz
  change b<f z ∧ f z<f w at hz
  let t := (f z-b)/(f w-b)
  have hd : 0<f w-b := sub_pos.mpr hb
  have ht : 0<t := div_pos (sub_pos.mpr hz.1) hd
  have ht1 : t<1 := (div_lt_one hd).mpr (by linarith)
  let x := (1-t)⁻¹ • (z-t • w)
  have hx : f x=b := by
    dsimp [x]
    simp only [map_smul,map_sub,smul_eq_mul]
    have he : t*(f w-b)=f z-b := by dsimp [t]; field_simp
    rw [←div_eq_inv_mul,div_eq_iff (by linarith : 1-t≠0)]
    nlinarith
  have hm := hK (hP hx) hw (sub_nonneg.mpr ht1.le) ht.le (show 1-t+t=1 by ring)
  convert hm using 1
  dsimp [x]
  rw [smul_smul,mul_inv_cancel₀ (by linarith : 1-t≠0),one_smul]
  abel

lemma slab_interior (f : E →L[ℝ] ℝ) (b:ℝ) {K:Set E} (hK:Convex ℝ K)
    (hP : {x:E | f x=b}⊆K) {w:E} (hw:w∈K) (hb:b<f w) :
    {z:E | b<f z ∧ f z<f w}⊆interior K := by
  have ho : IsOpen {z:E | b<f z ∧ f z<f w} :=
    (isOpen_lt continuous_const f.continuous).inter (isOpen_lt f.continuous continuous_const)
  rw [←ho.interior_eq]
  exact interior_mono (slab_subset_convex f b hK hP hw hb)

lemma maxFree_hyperplane_of_dense (Γ:AddSubgroup E) (f:E →L[ℝ] ℝ) (hf:f≠0)
    (hd : Dense (f '' (Γ:Set E))) (b:ℝ) : MaxFree Γ {x:E | f x=b} := by
  have hpconv : Convex ℝ {x:E | f x=b} := (convex_singleton b).linear_preimage f.toLinearMap
  refine ⟨⟨hpconv,by simp [hyperplane_interior f hf b]⟩,?_⟩
  intro K hK hPK
  apply Subset.antisymm _ hPK
  intro w hw
  by_contra hn
  change f w≠b at hn
  have bad (g:E →L[ℝ] ℝ) (a:ℝ) (hgp : {x:E | g x=a}⊆K)
      (hgd : Dense (g '' (Γ:Set E))) (ha:a<g w) : False := by
    obtain ⟨r,⟨z,hz,rfl⟩,hr⟩ := hgd.exists_mem_open (U := Ioo a (g w)) isOpen_Ioo
      ⟨(a+g w)/2,by constructor <;> linarith⟩
    exact hK.2 z (slab_interior g a hK.1 hgp hw ha hr) hz
  rcases lt_or_gt_of_ne hn with hlt|hgt
  · apply bad (-f) (-b)
    · simpa using hPK
    · have hh := (Homeomorph.neg ℝ).surjective.denseRange.dense_image (Homeomorph.neg ℝ).continuous hd
      simpa [image_image,Function.comp_def] using hh
    · simpa using neg_lt_neg hlt
  · exact bad f b hPK hd hgt

end MaxLatticeFree.Geometry.Proof
-- End HyperplaneGeometry

-- Begin KernelSpan

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma kernel_span_of_nondense (Γ : AddSubgroup E) (hspan : Submodule.span ℝ (Γ:Set E)=⊤)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) (hn : ¬ Dense (f '' (Γ:Set E))) :
    Submodule.span ℝ ((Γ:Set E) ∩ (LinearMap.ker f.toLinearMap : Set E)) =
      LinearMap.ker f.toLinearMap := by
  let H := Γ.map f.toLinearMap.toAddMonoidHom
  obtain ⟨a,ha⟩ := H.dense_or_cyclic.resolve_left hn
  have haH : a ∈ H := by rw [ha]; exact AddSubgroup.subset_closure (mem_singleton a)
  obtain ⟨v,hv,hfv⟩ := AddSubgroup.mem_map.mp haH
  change f v = a at hfv
  have ha0 : a ≠ 0 := by
    intro hz
    have hzΓ : ∀ x ∈ Γ, f x = 0 := by
      intro x hx
      have hm : f x ∈ H := AddSubgroup.mem_map.mpr ⟨x,hx,rfl⟩
      rw [ha,hz,AddSubgroup.mem_closure_singleton] at hm
      obtain ⟨z,he⟩ := hm
      simpa using he.symm
    have hs : Submodule.span ℝ (Γ:Set E) ≤ LinearMap.ker f.toLinearMap :=
      Submodule.span_le.mpr hzΓ
    rw [hspan] at hs
    apply hf
    ext x
    exact hs (Submodule.mem_top)
  let K := Submodule.span ℝ ((Γ:Set E) ∩ (LinearMap.ker f.toLinearMap : Set E))
  let p : E →ₗ[ℝ] E := LinearMap.id - (f.toLinearMap.smulRight ((a⁻¹) • v))
  have hp (x:E) : p x = x - (f x / a) • v := by
    simp [p,div_eq_mul_inv,smul_smul]
  have hΓ (x:E) (hx:x∈Γ) : p x ∈ K := by
    have hm : f x ∈ H := AddSubgroup.mem_map.mpr ⟨x,hx,rfl⟩
    rw [ha,AddSubgroup.mem_closure_singleton] at hm
    obtain ⟨z,hz⟩ := hm
    have hfx : f x = (z:ℝ)*a := by simpa [zsmul_eq_mul] using hz.symm
    apply Submodule.subset_span
    constructor
    · rw [hp,hfx,mul_div_cancel_right₀ _ ha0,Int.cast_smul_eq_zsmul]
      exact Γ.sub_mem hx (Γ.zsmul_mem hv z)
    · change f (p x)=0
      rw [hp]
      simp [hfv,ha0]
  have hall : ∀ x:E,p x∈K := by
    intro x
    have hx : x∈Submodule.span ℝ (Γ:Set E) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hΓ x hx
    | zero => simp
    | add x y _ _ hx hy => simpa using K.add_mem hx hy
    | smul c x _ hx => simpa using K.smul_mem c hx
  apply le_antisymm (Submodule.span_le.mpr inter_subset_right)
  intro x hx
  have hh := hall x
  simpa [hp,show f x=0 from hx] using hh

end MaxLatticeFree.Geometry.Proof
-- End KernelSpan

-- Begin DiscreteFinite

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E]

lemma finite_compact_inter_group (Γ : AddSubgroup E)
    (hΓ : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0)
    {K : Set E} (hK : IsCompact K) : (K ∩ (Γ : Set E)).Finite := by
  obtain ⟨ε, hε, hg⟩ := hΓ
  obtain ⟨t, ht, hfin, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (hK.totallyBounded.subset inter_subset_left) ε hε
  apply hfin.subset
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hyΓ : y ∈ Γ := (ht hy).2
  have he : x - y = 0 := hg (x-y) (Γ.sub_mem hx.2 hyΓ) (by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxy)
  exact (sub_eq_zero.mp he) ▸ hy

end MaxLatticeFree.Geometry.Proof
-- End DiscreteFinite

-- Begin KernelRounding

open Set Metric
open scoped BigOperators
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma kernel_rounding_compact (Γ : AddSubgroup E) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    {I : Type*} [Fintype I] (b : Module.Basis I ℝ (LinearMap.ker f.toLinearMap))
    (hb : ∀ i, (b i : E) ∈ Γ) :
    ∃ K : Set E, IsCompact K ∧ ∀ x ∈ Γ, |f x| ≤ 1 → ∃ y ∈ K ∩ (Γ:Set E), f y = f x := by
  classical
  obtain ⟨e,he⟩ := functional_unit f hf
  let F : ℝ × (I → ℝ) → E := fun s => s.1 • e + ∑ i, s.2 i • (b i : E)
  have hF : Continuous F := by dsimp [F]; fun_prop
  let K := F '' Icc ((-1:ℝ),(0:I→ℝ)) (1,1)
  refine ⟨K,isCompact_Icc.image hF,?_⟩
  intro x hx hfx
  let p : LinearMap.ker f.toLinearMap := ⟨x - f x • e, by simp [he]⟩
  let z : E := ∑ i, ⌊b.repr p i⌋ • (b i : E)
  let y := x-z
  have hzΓ : z ∈ Γ := Γ.sum_mem (fun i _ => Γ.zsmul_mem (hb i) _)
  have hzf : f z = 0 := by
    dsimp [z]
    simp only [map_sum,map_zsmul]
    apply Finset.sum_eq_zero
    intro i _
    simp [show f (b i : E) = 0 from (b i).property]
  have hrepr : ∑ i, (b.repr p i) • (b i : E) = x - f x • e := by
    have hh := congrArg (fun v : LinearMap.ker f.toLinearMap => (v:E)) (b.sum_repr p)
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using hh
  have hy : y = F (f x,fun i => Int.fract (b.repr p i)) := by
    dsimp [y,z,F]
    simp only [Int.fract,sub_smul,Finset.sum_sub_distrib,Int.cast_smul_eq_zsmul]
    rw [hrepr]
    abel
  refine ⟨y,⟨?_,Γ.sub_mem hx hzΓ⟩,?_⟩
  · rw [hy]
    refine ⟨_,?_,rfl⟩
    constructor
    · exact ⟨(abs_le.mp hfx).1, fun i => Int.fract_nonneg _⟩
    · exact ⟨(abs_le.mp hfx).2, fun i => (Int.fract_lt_one _).le⟩
  · simp [y,hzf]

lemma not_dense_of_kernel_basis (Γ : AddSubgroup E)
    (hΓ : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0)
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    {I : Type*} [Fintype I] (b : Module.Basis I ℝ (LinearMap.ker f.toLinearMap))
    (hb : ∀ i, (b i : E) ∈ Γ) : ¬ Dense (f '' (Γ:Set E)) := by
  obtain ⟨K,hK,hround⟩ := kernel_rounding_compact Γ f hf b hb
  let s := f '' (K ∩ (Γ:Set E))
  have hs : s.Finite := (finite_compact_inter_group Γ hΓ hK).image f
  have ho : IsOpen (s \ {0})ᶜ := (hs.sdiff).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho 0 (by simp)
  intro hd
  obtain ⟨r,⟨x,hx,hxr⟩,hr⟩ := hd.exists_mem_open (U := Ioo 0 (min ε 1)) isOpen_Ioo
    (nonempty_Ioo.mpr (lt_min hε zero_lt_one))
  have hxrbound : |f x| ≤ 1 := by rw [hxr,abs_of_pos hr.1]; exact (hr.2.trans_le (min_le_right _ _)).le
  obtain ⟨y,hy,he⟩ := hround x hx hxrbound
  have hrs : r ∈ s := ⟨y,hy,he.trans hxr⟩
  have hrball : r ∈ ball (0:ℝ) ε := by
    simpa [mem_ball,dist_eq_norm,Real.norm_eq_abs,abs_of_pos hr.1] using hr.2.trans_le (min_le_left _ _)
  exact hball hrball ⟨hrs,by simpa using hr.1.ne'⟩

end MaxLatticeFree.Geometry.Proof
-- End KernelRounding

-- Begin LatticeDiscrete

open Set Metric
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma integer_span_discrete {I : Type*} [Finite I] (b : Module.Basis I ℝ E) :
    ∃ε:ℝ, 0<ε ∧ ∀x∈Submodule.span ℤ (range b), ‖x‖<ε → x=0 := by
  let L := Submodule.span ℤ (range b)
  have ho : IsOpen ({0}:Set L) := isOpen_discrete _
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho 0 (mem_singleton 0)
  refine ⟨ε,hε,?_⟩
  intro x hx hn
  have h : (⟨x,hx⟩:L)∈({0}:Set L) := hball (by simpa [mem_ball,dist_eq_norm] using hn)
  exact congrArg Subtype.val (mem_singleton_iff.mp h)

lemma independent_closure_discrete {I : Type*} (a : I → E) (ha : LinearIndependent ℝ a) :
    ∃ε:ℝ,0<ε ∧ ∀x∈AddSubgroup.closure (range a),‖x‖<ε → x=0 := by
  classical
  let b := Module.Basis.extend ha.linearIndepOn_id
  let := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ E)
  obtain ⟨ε,hε,hb⟩ := integer_span_discrete b
  have hsub : AddSubgroup.closure (range a)≤(Submodule.span ℤ (range b)).toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    apply Submodule.subset_span
    rw [Module.Basis.range_extend]
    exact Module.Basis.subset_extend ha.linearIndepOn_id hx
  exact ⟨ε,hε,fun x hx hn=>hb x (hsub hx) hn⟩

lemma native_lattice_discrete {n:ℕ} {Γ:AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V:Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) :
    ∃ε:ℝ,0<ε ∧ ∀x∈Γ,‖x‖<ε → x=0 := by
  obtain ⟨m,a,ha,_,rfl⟩ := h
  exact independent_closure_discrete a ha

lemma native_lattice_subset {n:ℕ} {Γ:AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V:Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) : (Γ : Set (EuclideanSpace ℝ (Fin n))) ⊆ (V : Set (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨m,a,_,hspan,rfl⟩ := h
  change AddSubgroup.closure (range a) ≤ V.toAddSubgroup
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rw [←hspan]
  exact Submodule.subset_span hx

lemma native_lattice_span {n:ℕ} {Γ:AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V:Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) :
    Submodule.span ℝ (Γ:Set _) = V := by
  apply le_antisymm (Submodule.span_le.mpr (native_lattice_subset h))
  obtain ⟨m,a,_,hspan,rfl⟩ := h
  rw [←hspan]
  exact Submodule.span_mono AddSubgroup.subset_closure

end MaxLatticeFree.Geometry.Proof
-- End LatticeDiscrete

-- Begin LatticeSpanAdapters

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma subtype_span_top (Γ : AddSubgroup E) (L : Submodule ℝ E)
    (h : Submodule.span ℝ ((Γ:Set E) ∩ (L:Set E)) = L) :
    Submodule.span ℝ {x:L | (x:E)∈Γ} = ⊤ := by
  apply Submodule.map_injective_of_injective L.injective_subtype
  rw [Submodule.map_span,Submodule.map_subtype_top]
  have he : L.subtype '' {x:L | (x:E)∈Γ} = (Γ:Set E) ∩ (L:Set E) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [he,h]

lemma finite_basis_in_group (Γ : AddSubgroup E) (L : Submodule ℝ E)
    (h : Submodule.span ℝ ((Γ:Set E) ∩ (L:Set E)) = L) :
    ∃ k : ℕ, ∃ b : Fin k → E, LinearIndependent ℝ b ∧
      Submodule.span ℝ (range b) = L ∧ ∀ i, b i ∈ Γ := by
  classical
  let b := Module.Basis.ofSpan (show (⊤:Submodule ℝ L) ≤ Submodule.span ℝ {x:L | (x:E)∈Γ} by
    rw [subtype_span_top Γ L h])
  let := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ L)
  have hb : ∀ i, (b i:E) ∈ Γ := by
    intro i
    have hh : b i ∈ {x:L | (x:E)∈Γ} := Module.Basis.ofSpan_subset _ ⟨i,rfl⟩
    exact hh
  let c := b.reindex (Fintype.equivFin _)
  refine ⟨_,fun i => (c i:E),?_,?_,?_⟩
  · exact c.linearIndependent.map' L.subtype (LinearMap.ker_eq_bot.mpr L.injective_subtype)
  · have hh := congrArg (Submodule.map L.subtype) c.span_eq
    simpa only [Submodule.map_span,←range_comp,Function.comp_def,Submodule.map_subtype_top,Submodule.coe_subtype] using hh
  · intro i
    change ((b.reindex (Fintype.equivFin _)) i : E) ∈ Γ
    rw [Module.Basis.reindex_apply]
    exact hb _

lemma native_lambdaSubspace_iff_span {n : ℕ}
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    IsLambdaSubspace Γ V L ↔ L ≤ V ∧ Submodule.span ℝ ((Γ:Set _) ∩ (L:Set _)) = L := by
  constructor
  · rintro ⟨hLV,k,b,hb,hs,hΓ⟩
    refine ⟨hLV,le_antisymm (Submodule.span_le.mpr inter_subset_right) ?_⟩
    rw [←hs]
    apply Submodule.span_mono
    rintro x ⟨i,rfl⟩
    refine ⟨hΓ i,?_⟩
    exact Submodule.subset_span (mem_range_self i)
  · rintro ⟨hLV,hs⟩
    exact ⟨hLV,finite_basis_in_group Γ L hs⟩

end MaxLatticeFree.Geometry.Proof
-- End LatticeSpanAdapters

-- Begin RationalKernel

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma dense_image_iff_kernel_not_spanned (Γ : AddSubgroup E)
    (hΓ : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0)
    (hspan : Submodule.span ℝ (Γ:Set E)=⊤) (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    Dense (f '' (Γ:Set E)) ↔
      Submodule.span ℝ ((Γ:Set E) ∩ (LinearMap.ker f.toLinearMap : Set E)) ≠
        LinearMap.ker f.toLinearMap := by
  classical
  constructor
  · intro hd hs
    let L := LinearMap.ker f.toLinearMap
    let b := Module.Basis.ofSpan (show (⊤:Submodule ℝ L) ≤ Submodule.span ℝ {x:L | (x:E)∈Γ} by
      rw [subtype_span_top Γ L hs])
    let := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ L)
    have hb : ∀ i, (b i:E)∈Γ := by
      intro i
      have hh : b i ∈ {x:L | (x:E)∈Γ} := Module.Basis.ofSpan_subset _ ⟨i,rfl⟩
      exact hh
    exact not_dense_of_kernel_basis Γ hΓ f hf b hb hd
  · intro hn
    by_contra hd
    exact hn (kernel_span_of_nondense Γ hspan f hf hd)

end MaxLatticeFree.Geometry.Proof
-- End RationalKernel

-- Begin NativeLatticeAdapters

open Set
namespace MaxLatticeFree.Geometry.Proof

lemma native_lattice_comap_span {n : ℕ} {Γ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) :
    Submodule.span ℝ (Γ.comap V.subtype.toAddMonoidHom : Set V) = ⊤ := by
  apply subtype_span_top Γ V
  have he : (Γ : Set (EuclideanSpace ℝ (Fin n))) ∩ (V:Set _) = Γ :=
    inter_eq_left.mpr (native_lattice_subset h)
  rw [he,native_lattice_span h]

lemma native_lattice_comap_discrete {n : ℕ} {Γ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ.comap V.subtype.toAddMonoidHom, ‖g‖ < ε → g = 0 := by
  obtain ⟨ε,hε,hg⟩ := native_lattice_discrete h
  exact ⟨ε,hε,fun g hm hn => Subtype.ext (hg g hm hn)⟩

lemma native_lambdaSubspace_map_iff {n : ℕ}
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ V) :
    IsLambdaSubspace Γ V (L.map V.subtype) ↔
      Submodule.span ℝ ((Γ.comap V.subtype.toAddMonoidHom : Set V) ∩ (L:Set V)) = L := by
  rw [native_lambdaSubspace_iff_span]
  have hle : L.map V.subtype ≤ V := by
    rintro x ⟨y,hy,rfl⟩; exact y.property
  simp only [hle,true_and]
  have he : V.subtype '' ((Γ.comap V.subtype.toAddMonoidHom:Set V) ∩ (L:Set V)) =
      (Γ:Set _) ∩ (L.map V.subtype:Set _) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy.1,⟨y,hy.2,rfl⟩⟩
    · rintro ⟨hx,y,hy,he⟩
      exact ⟨y,⟨by change V.subtype y ∈ Γ; rw [he]; exact hx,hy⟩,he⟩
  rw [←he,←Submodule.map_span]
  exact (Submodule.map_injective_of_injective V.injective_subtype).eq_iff

lemma native_dense_iff_kernel_not_lambda {n : ℕ}
    {Γ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V)
    (f : V →L[ℝ] ℝ) (hf : f ≠ 0) :
    Dense (f '' (Γ.comap V.subtype.toAddMonoidHom : Set V)) ↔
      ¬ IsLambdaSubspace Γ V ((LinearMap.ker f.toLinearMap).map V.subtype) := by
  rw [native_lambdaSubspace_map_iff]
  exact dense_image_iff_kernel_not_spanned _ (native_lattice_comap_discrete h)
    (native_lattice_comap_span h) f hf

end MaxLatticeFree.Geometry.Proof
-- End NativeLatticeAdapters

-- Begin HyperplaneCriterion

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma maxFree_hyperplane_iff_dense (Γ : AddSubgroup E) (f : E →L[ℝ] ℝ)
    (hf : f ≠ 0) (b : ℝ) :
    MaxFree Γ {x : E | f x = b} ↔ Dense (f '' (Γ : Set E)) := by
  refine ⟨?_, fun hd => maxFree_hyperplane_of_dense Γ f hf hd b⟩
  intro hmax
  by_contra hn
  let H := Γ.map f.toLinearMap.toAddMonoidHom
  have hH : ¬ Dense (H : Set ℝ) := hn
  obtain ⟨l,u,hlu,hb,hgap⟩ := nondense_real_group_slab H hH b
  obtain ⟨e,he⟩ := functional_unit f hf
  have hsur : Function.Surjective f := fun r => ⟨r • e, by simp [he]⟩
  have ho := f.isOpenMap hsur
  let K : Set E := f ⁻¹' Icc l u
  have hint : interior K = f ⁻¹' Ioo l u := by
    rw [←ho.preimage_interior_eq_interior_preimage f.continuous (Icc l u), interior_Icc]
  have hK : Free Γ K := by
    refine ⟨(convex_Icc l u).linear_preimage f.toLinearMap, ?_⟩
    intro x hx hxΓ
    rw [hint] at hx
    exact hgap (f x) (AddSubgroup.mem_map.mpr ⟨x,hxΓ,rfl⟩) hx
  have hsub : {x : E | f x = b} ⊆ K := by
    intro x hx
    change f x = b at hx
    change f x ∈ Icc l u
    simpa [hx] using hb
  have heq := hmax.2 K hK hsub
  have hm : ((l+u)/2) • e ∈ interior K := by
    rw [hint]
    simp only [mem_preimage,map_smul,he,smul_eq_mul,mul_one,mem_Ioo]
    constructor <;> linarith
  rw [heq,hyperplane_interior f hf b] at hm
  exact hm

end MaxLatticeFree.Geometry.Proof
-- End HyperplaneCriterion

-- Begin HyperplaneLinearAlgebra

namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma functional_kernel_codim (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    Module.finrank ℝ (LinearMap.ker f.toLinearMap) + 1 = Module.finrank ℝ E := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro h
  exact hf (ContinuousLinearMap.coe_injective h)

lemma functional_of_codim_one (L : Submodule ℝ E)
    (hd : Module.finrank ℝ L + 1 = Module.finrank ℝ E) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ LinearMap.ker f.toLinearMap = L := by
  have hL : L ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hd
    omega
  have hp : Lᗮ ≠ ⊥ := fun h => hL (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  let f : E →L[ℝ] ℝ := innerSL ℝ v
  have hf : f ≠ 0 := by
    intro h
    have hh := congrArg (fun g : E →L[ℝ] ℝ => g v) h
    exact hv0 (by simpa [f] using hh)
  refine ⟨f,hf,?_⟩
  have hle : L ≤ LinearMap.ker f.toLinearMap := by
    intro x hx
    change inner ℝ v x = 0
    rw [←real_inner_comm v x]
    exact L.inner_right_of_mem_orthogonal hx hv
  have hk := functional_kernel_codim f hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end MaxLatticeFree.Geometry.Proof
-- End HyperplaneLinearAlgebra

-- Begin HyperplaneTransport

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma image_level_eq_vadd_kernel (W : Submodule ℝ E) (f : W →L[ℝ] ℝ) (v : W) :
    (Subtype.val : W → E) '' {x : W | f x = f v} =
      (v:E) +ᵥ ((LinearMap.ker f.toLinearMap).map W.subtype : Set E) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change f y = f v at hy
    refine ⟨(y:E)-(v:E),?_,by simp⟩
    refine ⟨y-v,?_,rfl⟩
    change f (y-v)=0
    simp only [map_sub,hy,sub_self]
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨v+z,?_,by simp⟩
    change f (v+z)=f v
    change f z=0 at hz
    simp [hz]

lemma preimage_vadd_eq_level (W : Submodule ℝ E) (f : W →L[ℝ] ℝ) (v : W) :
    (Subtype.val : W → E) ⁻¹' ((v:E) +ᵥ ((LinearMap.ker f.toLinearMap).map W.subtype:Set E)) =
      {x : W | f x=f v} := by
  rw [←image_level_eq_vadd_kernel]
  exact preimage_image_eq _ Subtype.val_injective

lemma map_subtype_comap_eq (W L : Submodule ℝ E) (hLW : L ≤ W) :
    (L.comap W.subtype).map W.subtype = L := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx; exact ⟨⟨x,hLW hx⟩,hx,rfl⟩

end MaxLatticeFree.Geometry.Proof
-- End HyperplaneTransport

open MaxLatticeFree.Geometry MaxLatticeFree.Geometry.Proof

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V)
    (hdim : Module.finrank ℝ L + 1 = Module.finrank ℝ V) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V) :
    IsMaxLambdaFree Λ V (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) ↔ ¬ IsLambdaSubspace Λ V L := by
  let K := L.comap V.subtype
  have hKmap : K.map V.subtype = L := map_subtype_comap_eq V L hLV
  have hKdim : Module.finrank ℝ K + 1 = Module.finrank ℝ V := by
    have he := (Submodule.equivMapOfInjective V.subtype V.injective_subtype K).finrank_eq
    rw [hKmap] at he
    omega
  obtain ⟨f, hf, hker⟩ := functional_of_codim_one K hKdim
  have hmap : (LinearMap.ker f.toLinearMap).map V.subtype = L := by rw [hker, hKmap]
  have hsub : v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ⊆ (V : Set _) := by
    rintro x ⟨y, hy, rfl⟩
    exact V.add_mem hv (hLV hy)
  have hpre : (Subtype.val : V → _) ⁻¹' (v +ᵥ (L : Set _)) =
      {x : V | f x = f ⟨v, hv⟩} := by
    rw [← hmap]
    exact preimage_vadd_eq_level V f ⟨v, hv⟩
  rw [nativeMaxFree_iff Λ V _ hsub, hpre, maxFree_hyperplane_iff_dense _ f hf,
    native_dense_iff_kernel_not_lambda hΛ f hf, hmap]
