-- Prove2me | solution 1 for MaxLatticeFree.Geometry.maxLambdaFree_in_W_iff
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T22:12:06.225815+00:00
-- url     : https://prove2.me/submissions/fe37f171-6a7a-45e8-b259-ee963587c72a

-- Complete checked reconstruction of the native three-case maximal lattice-free classification.
-- Licensed under Apache 2.0.
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Mathlib


-- Begin PolyBody

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

def polyBody (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}

lemma polyBody_convex (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (polyBody a b) := by
  intro x hx y hy s t hs ht hsum i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    s*a i x+t*a i y ≤ s*b i+t*b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul,hsum,one_mul]

end MaxLatticeFree.Geometry.Proof
-- End PolyBody

-- Begin PolyTopology

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma polyBody_closed (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : IsClosed (polyBody a b) := by
  unfold polyBody
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (a i).continuous_of_finiteDimensional continuous_const

lemma strict_mem_interior (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) {x : E}
    (hx : ∀ i, a i x < b i) : x ∈ interior (polyBody a b) := by
  let U : Set E := {y | ∀ i, a i y < b i}
  have hU : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (a i).continuous_of_finiteDimensional continuous_const
  have hsub : U ⊆ polyBody a b := fun y hy i => (hy i).le
  exact interior_maximal hsub hU hx

end MaxLatticeFree.Geometry.Proof
-- End PolyTopology

-- Begin PolyInterior

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma interior_polyBody_strict (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) {x : E} (hx : x ∈ interior (polyBody a b)) :
    ∀ i, a i x < b i := by
  intro i
  let f : E →L[ℝ] ℝ := (a i).toContinuousLinearMap
  have hf : f ≠ 0 := by
    intro h
    apply ha i
    ext y
    have he := congrArg (fun g : E →L[ℝ] ℝ => g y) h
    simpa [f] using he
  have hopen : IsOpen (f '' interior (polyBody a b)) :=
    f.isOpenMap_of_ne_zero hf _ isOpen_interior
  have hsub : f '' interior (polyBody a b) ⊆ Iic (b i) := by
    rintro _ ⟨y, hy, rfl⟩
    exact interior_subset hy i
  have hmem : f x ∈ interior (Iic (b i)) :=
    interior_maximal hsub hopen (mem_image_of_mem f hx)
  simpa [f] using hmem

lemma mem_interior_polyBody_iff (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) {x : E} :
    x ∈ interior (polyBody a b) ↔ ∀ i, a i x < b i :=
  ⟨interior_polyBody_strict a b ha, strict_mem_interior a b⟩

end MaxLatticeFree.Geometry.Proof
-- End PolyInterior

-- Begin PolyCoercive

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

noncomputable def positiveRowSum (a : ι → E →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  ∑ i, max 0 (a i x)

lemma positiveRowSum_continuous (a : ι → E →ₗ[ℝ] ℝ) : Continuous (positiveRowSum a) := by
  unfold positiveRowSum
  exact continuous_finsetSum _ fun i _ => continuous_const.max (a i).continuous_of_finiteDimensional

omit [FiniteDimensional ℝ E] in
lemma positiveRowSum_pos (a : ι → E →ₗ[ℝ] ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) {x : E} (hx : x≠0) : 0 < positiveRowSum a x := by
  have hn : 0 ≤ positiveRowSum a x := Finset.sum_nonneg fun i _ => le_max_left _ _
  by_contra hp
  have he : positiveRowSum a x=0 := le_antisymm (le_of_not_gt hp) hn
  apply hx
  apply hz
  intro i
  have hh : max 0 (a i x) ≤ positiveRowSum a x :=
    Finset.single_le_sum (fun j _ => le_max_left (0:ℝ) (a j x)) (Finset.mem_univ i)
  rw [he] at hh
  exact (le_max_right _ _).trans hh

omit [FiniteDimensional ℝ E] in
lemma positiveRowSum_smul (a : ι → E →ₗ[ℝ] ℝ) {c : ℝ} (hc : 0≤c) (x : E) :
    positiveRowSum a (c • x) = c * positiveRowSum a x := by
  simp only [positiveRowSum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ hc,mul_zero]

lemma positiveRowSum_coercive [Nontrivial E] (a : ι → E →ₗ[ℝ] ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x, δ*‖x‖ ≤ positiveRowSum a x := by
  obtain ⟨u,hu⟩ := exists_norm_eq (E:=E) (show (0:ℝ)≤1 by norm_num)
  have hne : (Metric.sphere (0:E) 1).Nonempty := ⟨u,by simpa using hu⟩
  obtain ⟨v,hv,hmin⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn hne
    (positiveRowSum_continuous a).continuousOn
  have hvn : ‖v‖=1 := by simpa using hv
  have hv0 : v≠0 := by intro h; simp [h] at hvn
  refine ⟨positiveRowSum a v,positiveRowSum_pos a hz hv0,fun x => ?_⟩
  by_cases hx : x=0
  · subst x; simp [positiveRowSum]
  have hxn : 0<‖x‖ := norm_pos_iff.mpr hx
  have hw : (‖x‖⁻¹:ℝ) • x ∈ Metric.sphere (0:E) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hxn]
    exact inv_mul_cancel₀ hxn.ne'
  have hh : positiveRowSum a v ≤ positiveRowSum a ((‖x‖⁻¹:ℝ) • x) := hmin hw
  rw [positiveRowSum_smul a (inv_nonneg.mpr hxn.le)] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hxn.le
  field_simp at hh'
  exact hh'

lemma polyBody_bounded (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) : Bornology.IsBounded (polyBody a b) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · apply isBounded_iff_forall_norm_le.mpr
    exact ⟨0,fun x _ => by rw [Subsingleton.elim x 0,norm_zero]⟩
  obtain ⟨δ,hδ,hbound⟩ := positiveRowSum_coercive a hz
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(∑ i, max 0 (b i))/δ,fun x hx => ?_⟩
  apply (le_div_iff₀ hδ).mpr
  have hh : positiveRowSum a x ≤ ∑ i,max 0 (b i) :=
    Finset.sum_le_sum fun i _ => max_le_max le_rfl (hx i)
  nlinarith [hbound x]

lemma polyBody_compact (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hz : ∀ x, (∀ i, a i x ≤ 0) → x=0) : IsCompact (polyBody a b) :=
  Metric.isCompact_of_isClosed_isBounded (polyBody_closed a b) (polyBody_bounded a b hz)

end MaxLatticeFree.Geometry.Proof
-- End PolyCoercive

-- Begin PolyFinite

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite intersection of closed linear halfspaces, in the current space. -/
def Polyhedral (S : Set E) : Prop :=
  ∃ (t : ℕ) (a : Fin t → E →ₗ[ℝ] ℝ) (b : Fin t → ℝ), S = polyBody a b

omit [FiniteDimensional ℝ E] in
lemma polyhedral_polyBody {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Polyhedral (polyBody a b) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, a ∘ e.symm, b ∘ e.symm, ?_⟩
  ext x
  constructor
  · intro hx i; exact hx (e.symm i)
  · intro hx i; simpa only [Function.comp_apply, e.symm_apply_apply] using hx (e i)

omit [FiniteDimensional ℝ E] in
lemma polyhedral_inter {S T : Set E} (hS : Polyhedral S) (hT : Polyhedral T) :
    Polyhedral (S ∩ T) := by
  classical
  obtain ⟨s,a,b,rfl⟩ := hS
  obtain ⟨t,c,d,rfl⟩ := hT
  have he : polyBody a b ∩ polyBody c d = polyBody (Sum.elim a c) (Sum.elim b d) := by
    ext x
    simp [polyBody]
  rw [he]
  exact polyhedral_polyBody _ _

lemma exists_compact_outer_poly {K : Set E} (hK : Bornology.IsBounded K) :
    ∃ P : Set E, Polyhedral P ∧ IsCompact P ∧ K ⊆ interior P := by
  classical
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hK
  let v := Module.finBasis ℝ E
  let a : (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → E →ₗ[ℝ] ℝ :=
    Sum.elim (fun i => v.coord i) (fun i => -v.coord i)
  let b := fun i => ‖(a i).toContinuousLinearMap‖ * R + 1
  refine ⟨polyBody a b, polyhedral_polyBody a b, polyBody_compact a b ?_, ?_⟩
  · intro x hx
    apply v.ext_elem
    intro i
    have hp := hx (Sum.inl i)
    have hn := hx (Sum.inr i)
    change v.repr x i = v.repr 0 i
    simp only [map_zero, Finsupp.zero_apply]
    change v.repr x i ≤ 0 at hp
    change -(v.repr x i) ≤ 0 at hn
    linarith
  · intro x hx
    apply strict_mem_interior
    intro i
    have hbound := (a i).toContinuousLinearMap.le_opNorm x
    have hmul := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg (a i).toContinuousLinearMap)
    have hle : a i x ≤ ‖(a i).toContinuousLinearMap‖ * R := by
      have hb : |a i x| ≤ ‖(a i).toContinuousLinearMap‖ * ‖x‖ := by
        simpa using hbound
      exact (le_abs_self _).trans (hb.trans hmul)
    change a i x < ‖(a i).toContinuousLinearMap‖ * R + 1
    linarith

end MaxLatticeFree.Geometry.Proof
-- End PolyFinite

-- Begin IrredundantSystem

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma polyhedral_irredundant {S : Set E} (hS : Polyhedral S) :
    ∃ (t : ℕ) (a : Fin t → E →ₗ[ℝ] ℝ) (b : Fin t → ℝ),
      S = polyBody a b ∧
      ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j := by
  classical
  obtain ⟨t,a,b,hS⟩ := hS
  let body := fun s : Finset (Fin t) => {x : E | ∀ i ∈ s, a i x ≤ b i}
  let good := Finset.univ.powerset.filter (fun s => body s = S)
  have huniv : Finset.univ ∈ good := by
    simp only [good,Finset.mem_filter,Finset.mem_powerset,Finset.subset_univ,true_and]
    simpa [body,polyBody] using hS.symm
  obtain ⟨s,hs,hmin⟩ := good.exists_min_image Finset.card ⟨_,huniv⟩
  have hsbody : body s = S := (Finset.mem_filter.mp hs).2
  have hwitness : ∀ i ∈ s, ∃ x : E, b i < a i x ∧ ∀ j ∈ s, j ≠ i → a j x ≤ b j := by
    intro i hi
    by_contra hh
    push Not at hh
    have he : body (s.erase i) = S := by
      rw [← hsbody]
      ext x
      constructor
      · intro hx j hj
        by_cases hji : j = i
        · subst j
          by_contra hbad
          have hl : b i < a i x := lt_of_not_ge hbad
          obtain ⟨j,hj,hji,hviol⟩ := hh x hl
          exact (not_le_of_gt hviol) (hx j (Finset.mem_erase.mpr ⟨hji,hj⟩))
        · exact hx j (Finset.mem_erase.mpr ⟨hji,hj⟩)
      · intro hx j hj
        exact hx j (Finset.mem_of_mem_erase hj)
    have herase : s.erase i ∈ good := by
      simp only [good,Finset.mem_filter,Finset.mem_powerset,Finset.subset_univ,true_and]
      exact he
    exact (not_le_of_gt (Finset.card_erase_lt_of_mem hi)) (hmin _ herase)
  let e := Fintype.equivFin s
  let aa : Fin (Fintype.card s) → E →ₗ[ℝ] ℝ := fun j => a (e.symm j)
  let bb : Fin (Fintype.card s) → ℝ := fun j => b (e.symm j)
  refine ⟨Fintype.card s,aa,bb,?_,?_⟩
  · rw [← hsbody]
    ext x
    constructor
    · intro hx j
      exact hx _ (e.symm j).property
    · intro hx i hi
      simpa [aa,bb] using hx (e ⟨i,hi⟩)
  · intro i
    obtain ⟨x,hx,hothers⟩ := hwitness (e.symm i) (e.symm i).property
    refine ⟨x,hx,fun j hji => hothers (e.symm j) (e.symm j).property ?_⟩
    intro he
    apply hji
    exact e.symm.injective (Subtype.ext he)

end MaxLatticeFree.Geometry.Proof
-- End IrredundantSystem

-- Begin StrictFacePoint

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma irredundant_rows_ne_zero (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hne : (polyBody a b).Nonempty)
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j) :
    ∀ i, a i ≠ 0 := by
  intro i hi
  obtain ⟨p,hp⟩ := hne
  obtain ⟨x,hx,_⟩ := hw i
  have hh := hp i
  simp only [hi,LinearMap.zero_apply] at hx hh
  linarith

omit [Fintype ι] in
lemma exists_strict_face_point (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hint : (interior (polyBody a b)).Nonempty)
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j)
    (i : ι) : ∃ y : E, a i y = b i ∧ ∀ j, j ≠ i → a j y < b j := by
  obtain ⟨p,hp⟩ := hint
  have hstrict := interior_polyBody_strict a b
    (irredundant_rows_ne_zero a b ⟨p,interior_subset hp⟩ hw) hp
  obtain ⟨x,hx,hothers⟩ := hw i
  let t : ℝ := (b i-a i p)/(a i x-a i p)
  have hd : 0 < a i x-a i p := by linarith [hstrict i]
  have ht : 0 < t := div_pos (by linarith [hstrict i]) hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  have he : t * (a i x-a i p) = b i-a i p := by
    exact div_mul_cancel₀ _ hd.ne'
  refine ⟨(1-t) • p+t • x,?_,?_⟩
  · simp only [map_add,map_smul,smul_eq_mul]
    nlinarith
  · intro j hji
    simp only [map_add,map_smul,smul_eq_mul]
    have h1 := mul_lt_mul_of_pos_left (hstrict j) (show 0 < 1-t by linarith)
    have h2 := mul_le_mul_of_nonneg_left (hothers j hji) ht.le
    nlinarith

end MaxLatticeFree.Geometry.Proof
-- End StrictFacePoint

-- Begin FiniteSlack

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    {a : ι → E →ₗ[ℝ] ℝ} {b : ι → ℝ} {v d : E}

lemma feasible_direction_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∀ᶠ t : ℝ in 𝓝 0, 0≤t → v+t • d ∈ polyBody a b := by
  have hh : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0≤t → a i (v+t • d)≤b i := by
    intro i
    by_cases hi : a i v=b i
    · exact Eventually.of_forall fun t ht=>by
        simp only [map_add,map_smul,smul_eq_mul,hi]
        exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht (hd i hi))
    · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
      have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
        have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
        simpa only [zero_mul,add_zero] using hcont.tendsto 0
      filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
      intro _
      simpa only [map_add,map_smul,smul_eq_mul] using ht.le
  filter_upwards [eventually_all.mpr hh] with t ht hpos i
  exact ht i hpos

lemma feasible_direction_step (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d≤0) :
    ∃ t : ℝ, 0<t ∧ v+t • d ∈ polyBody a b := by
  obtain ⟨t,ht,hf⟩ := (feasible_direction_nhds hv hd).exists_gt
  exact ⟨t,ht,hf ht.le⟩

lemma feasible_kernel_nhds (hv : v ∈ polyBody a b)
    (hd : ∀ i, a i v=b i → a i d=0) :
    ∀ᶠ t : ℝ in 𝓝 0, v+t • d ∈ polyBody a b := by
  apply eventually_all.mpr
  intro i
  by_cases hi : a i v=b i
  · exact Eventually.of_forall fun t=>by simp [map_add,map_smul,hi,hd i hi]
  · have hlt : a i v<b i := lt_of_le_of_ne (hv i) hi
    have hc : Tendsto (fun t : ℝ=>a i v+t*a i d) (𝓝 0) (𝓝 (a i v)) := by
      have hcont : Continuous (fun t : ℝ=>a i v+t*a i d) := by fun_prop
      simpa only [zero_mul,add_zero] using hcont.tendsto 0
    filter_upwards [hc.eventually (gt_mem_nhds hlt)] with t ht
    simpa only [map_add,map_smul,smul_eq_mul] using ht.le

end MaxLatticeFree.Geometry.Proof
-- End FiniteSlack

-- Begin RowFaceSpan

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι]

def rowFace (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι) : Set E :=
  {x | x ∈ polyBody a b ∧ a i x = b i}

lemma rowFace_direction (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι)
    {y : E} (hy : a i y = b i) (hstrict : ∀ j, j ≠ i → a j y < b j) :
    (affineSpan ℝ (rowFace a b i)).direction = LinearMap.ker (a i) := by
  classical
  have hyP : y ∈ polyBody a b := by
    intro j
    by_cases hji : j=i
    · simpa [hji] using hy.le
    · exact (hstrict j hji).le
  have hyF : y ∈ rowFace a b i := ⟨hyP,hy⟩
  have hspan : affineSpan ℝ (rowFace a b i) ≤
      AffineSubspace.mk' y (LinearMap.ker (a i)) := by
    apply affineSpan_le.mpr
    intro x hx
    change a i (x-y) = 0
    rw [map_sub,hx.2,hy,sub_self]
  apply le_antisymm
  · simpa only [AffineSubspace.direction_mk'] using AffineSubspace.direction_le hspan
  · intro d hd
    have hd0 : a i d = 0 := hd
    have hactive : ∀ j, a j y=b j → a j d=0 := by
      intro j hj
      by_cases hji : j=i
      · simpa [hji] using hd0
      · exact ((hstrict j hji).ne hj).elim
    obtain ⟨t,ht,hmem⟩ := (feasible_kernel_nhds hyP hactive).exists_gt
    have htF : y+t • d ∈ rowFace a b i := by
      refine ⟨hmem,?_⟩
      simp [map_add,map_smul,hy,hd0]
    have hv : t • d ∈ (affineSpan ℝ (rowFace a b i)).direction := by
      have hh := AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ htF) (subset_affineSpan ℝ _ hyF)
      simpa only [vsub_eq_sub,add_sub_cancel_left] using hh
    have hh := (affineSpan ℝ (rowFace a b i)).direction.smul_mem t⁻¹ hv
    simpa only [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] using hh

lemma rowFace_affineSpan (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι)
    {y : E} (hy : a i y = b i) (hstrict : ∀ j, j ≠ i → a j y < b j) :
    affineSpan ℝ (rowFace a b i) = AffineSubspace.mk' y (LinearMap.ker (a i)) := by
  rw [← rowFace_direction a b i hy hstrict]
  apply (AffineSubspace.mk'_eq _).symm
  apply subset_affineSpan
  refine ⟨?_,hy⟩
  intro j
  by_cases hji : j=i
  · simpa [hji] using hy.le
  · exact (hstrict j hji).le

end MaxLatticeFree.Geometry.Proof
-- End RowFaceSpan

-- Begin PolyStrictSelection

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι]

lemma exists_simultaneously_strict (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {F : Set E} (hF : Convex ℝ F) (hne : F.Nonempty)
    (hbound : ∀ x ∈ F, ∀ i, a i x ≤ b i)
    (hw : ∀ i, ∃ x ∈ F, a i x < b i) :
    ∃ y ∈ F, ∀ i, a i y < b i := by
  classical
  have hh : ∀ s : Finset ι, ∃ y ∈ F, ∀ i ∈ s, a i y < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y,hy⟩ := hne
      exact ⟨y,hy,by simp⟩
    | @insert i s _ ih =>
      obtain ⟨y,hy,hys⟩ := ih
      obtain ⟨x,hx,hxi⟩ := hw i
      refine ⟨(1/2:ℝ) • y+(1/2:ℝ) • x,hF hy hx (by norm_num) (by norm_num) (by norm_num),?_⟩
      intro j hj
      simp only [map_add,map_smul,smul_eq_mul]
      rcases Finset.mem_insert.mp hj with rfl | hj
      · linarith [hbound y hy j]
      · linarith [hys j hj,hbound x hx j]
  obtain ⟨y,hy,hh⟩ := hh Finset.univ
  exact ⟨y,hy,fun i => hh i (Finset.mem_univ i)⟩

end MaxLatticeFree.Geometry.Proof
-- End PolyStrictSelection

-- Begin GenericFacet

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def GFacet (S F : Set E) : Prop :=
  F.Nonempty ∧
  Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
    Module.finrank ℝ (affineSpan ℝ S).direction ∧
  ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ S, f x ≤ b) ∧ F = S ∩ {x | f x=b}

lemma GFacet.subset {S F : Set E} (h : GFacet S F) : F ⊆ S := by
  obtain ⟨_,_,f,b,_,rfl⟩ := h
  exact inter_subset_left

lemma GFacet.convex {S F : Set E} (h : GFacet S F) (hS : Convex ℝ S) : Convex ℝ F := by
  obtain ⟨_,_,f,b,_,rfl⟩ := h
  intro x hx y hy r s hr hs hrs
  refine ⟨hS hx.1 hy.1 hr hs hrs,?_⟩
  change f (r • x+s • y)=b
  have hxx : f x=b := hx.2
  have hyy : f y=b := hy.2
  simp only [map_add,map_smul,smul_eq_mul,hxx,hyy,← add_mul,hrs,one_mul]

lemma GFacet.functional_ne_zero {S F : Set E} (h : GFacet S F)
    {f : E →ₗ[ℝ] ℝ} {b : ℝ} (he : F=S ∩ {x | f x=b}) : f ≠ 0 := by
  intro hf
  obtain ⟨x,hx⟩ := h.1
  have hb : b=0 := by
    have hh := (show x ∈ S ∩ {x | f x=b} from he ▸ hx).2
    simpa [hf] using hh.symm
  have hFS : F=S := by simp [he,hf,hb]
  have hh := h.2.1
  rw [hFS] at hh
  omega

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma rowFace_is_gFacet (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hint : (interior (polyBody a b)).Nonempty)
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j)
    (i : ι) : GFacet (polyBody a b) (rowFace a b i) := by
  obtain ⟨y,hy,hstrict⟩ := exists_strict_face_point a b hint hw i
  have hyP : y ∈ polyBody a b := by
    intro j
    by_cases hj : j=i
    · simpa [hj] using hy.le
    · exact (hstrict j hj).le
  refine ⟨⟨y,hyP,hy⟩,?_,a i,b i,fun x hx => hx i,rfl⟩
  rw [rowFace_direction a b i hy hstrict,
    (polyBody_convex a b).interior_nonempty_iff_affineSpan_eq_top.mp hint,
    AffineSubspace.direction_top,finrank_top]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero
    (irredundant_rows_ne_zero a b ⟨y,hyP⟩ hw i)

lemma gFacet_eq_rowFace (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hint : (interior (polyBody a b)).Nonempty)
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j)
    {F : Set E} (hF : GFacet (polyBody a b) F) : ∃ i, F = rowFace a b i := by
  classical
  obtain ⟨f,c,hbound,he⟩ := hF.2.2
  have hf : f ≠ 0 := hF.functional_ne_zero he
  have hactive : ∃ i, ∀ x ∈ F, a i x=b i := by
    by_contra hn
    push Not at hn
    have hwit : ∀ i, ∃ x ∈ F, a i x < b i := by
      intro i
      obtain ⟨x,hx,hne⟩ := hn i
      exact ⟨x,hx,lt_of_le_of_ne (hF.subset hx i) hne⟩
    obtain ⟨x,hx,hstrict⟩ := exists_simultaneously_strict a b
      (hF.convex (polyBody_convex a b)) hF.1 (fun x hx i => hF.subset hx i) hwit
    have hxint := strict_mem_interior a b hstrict
    have hsub : polyBody a b ⊆ polyBody (fun _ : Unit => f) (fun _ => c) :=
      fun y hy _ => hbound y hy
    have hlt := interior_polyBody_strict (fun _ : Unit => f) (fun _ => c)
      (fun _ => hf) (interior_mono hsub hxint) ()
    have hxc := (show x ∈ polyBody a b ∩ {x | f x=c} from he ▸ hx).2
    exact hlt.ne hxc
  obtain ⟨i,hi⟩ := hactive
  have hsub : F ⊆ rowFace a b i := fun x hx => ⟨hF.subset hx,hi x hx⟩
  have hrow := rowFace_is_gFacet a b hint hw i
  have hle := affineSpan_mono ℝ hsub
  have hdir : (affineSpan ℝ F).direction = (affineSpan ℝ (rowFace a b i)).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (by
      have h1 := hF.2.1
      have h2 := hrow.2.1
      omega)
  have hspan : affineSpan ℝ F = affineSpan ℝ (rowFace a b i) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir (hF.1.affineSpan ℝ) hle
  obtain ⟨z,hz⟩ := hF.1
  have hzc : f z=c := (show z ∈ polyBody a b ∩ {x | f x=c} from he ▸ hz).2
  have hlevel : affineSpan ℝ F ≤ AffineSubspace.mk' z (LinearMap.ker f) := by
    apply affineSpan_le.mpr
    intro x hx
    change f (x-z)=0
    have hxc := (show x ∈ polyBody a b ∩ {x | f x=c} from he ▸ hx).2
    change f x=c at hxc
    simp [map_sub,hxc,hzc]
  refine ⟨i,Subset.antisymm hsub ?_⟩
  intro x hx
  have hxf := hlevel (hspan ▸ subset_affineSpan ℝ _ hx)
  change f (x-z)=0 at hxf
  rw [he]
  refine ⟨hx.1,?_⟩
  change f x=c
  rw [map_sub,hzc] at hxf
  linarith

end MaxLatticeFree.Geometry.Proof
-- End GenericFacet

-- Begin SubtypeDimension

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma direction_rank_subtype_image (W : Submodule ℝ E) (S : Set W) :
    Module.finrank ℝ (affineSpan ℝ (Subtype.val '' S : Set E)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have he : (Subtype.val '' S : Set E) = W.subtype.toAffineMap '' S := rfl
  rw [he,← AffineSubspace.map_span,AffineSubspace.map_direction]
  exact Submodule.finrank_map_subtype_eq W _

end MaxLatticeFree.Geometry.Proof
-- End SubtypeDimension

-- Begin NativeFacet

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma nativeFacet_iff_gFacet (S F : Set (EuclideanSpace ℝ (Fin n))) :
    IsFacet S F ↔ GFacet S F := by
  constructor
  · rintro ⟨hne,hd,a,b,hb,he⟩
    have hS : S.Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,(show x∈S ∩ {x | inner ℝ a x=b} from he ▸ hx).1⟩
    refine ⟨hne,?_,(innerSL ℝ a).toLinearMap,b,hb,he⟩
    simp only [affDim,if_pos hne,if_pos hS] at hd
    omega
  · rintro ⟨hne,hd,f,b,hb,he⟩
    have hS : S.Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,(show x∈S ∩ {x | f x=b} from he ▸ hx).1⟩
    let a := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f.toContinuousLinearMap
    have ha : ∀ x, inner ℝ a x=f x := by
      intro x
      simp [a]
    refine ⟨hne,?_,a,b,?_,?_⟩
    · simp only [affDim,if_pos hne,if_pos hS]
      omega
    · intro x hx
      rw [ha]
      exact hb x hx
    · simpa only [ha] using he

end MaxLatticeFree.Geometry.Proof
-- End NativeFacet

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

-- Begin SubtypeFacet

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma gFacet_subtype_image_iff (W : Submodule ℝ E) (S F : Set W) :
    GFacet (Subtype.val '' S : Set E) (Subtype.val '' F) ↔ GFacet S F := by
  constructor
  · rintro ⟨hne,hd,f,b,hbound,he⟩
    refine ⟨image_nonempty.mp hne,?_,f.comp W.subtype,b,?_,?_⟩
    · simpa only [direction_rank_subtype_image] using hd
    · intro x hx
      exact hbound x (mem_image_of_mem _ hx)
    · ext x
      constructor
      · intro hx
        have hh : (x:E) ∈ (Subtype.val '' S : Set E) ∩ {y | f y=b} :=
          he ▸ mem_image_of_mem Subtype.val hx
        refine ⟨?_,hh.2⟩
        obtain ⟨y,hy,hyx⟩ := hh.1
        exact (Subtype.val_injective hyx) ▸ hy
      · rintro ⟨hx,hfx⟩
        have hh : (x:E) ∈ (Subtype.val '' S : Set E) ∩ {y | f y=b} :=
          ⟨mem_image_of_mem _ hx,hfx⟩
        rw [← he] at hh
        obtain ⟨y,hy,hyx⟩ := hh
        exact (Subtype.val_injective hyx) ▸ hy
  · rintro ⟨hne,hd,f,b,hbound,he⟩
    let g : E →ₗ[ℝ] ℝ := f.comp W.orthogonalProjectionOnto.toLinearMap
    have hg : ∀ x : W, g (x:E)=f x := by
      intro x
      simp [g,W.orthogonalProjectionOnto_mem_subspace_eq_self]
    refine ⟨hne.image _,?_,g,b,?_,?_⟩
    · simpa only [direction_rank_subtype_image] using hd
    · rintro _ ⟨x,hx,rfl⟩
      rw [hg]
      exact hbound x hx
    · ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [he] at hy
        exact ⟨mem_image_of_mem _ hy.1,by simpa only [Set.mem_ofPred_eq,hg] using hy.2⟩
      · rintro ⟨⟨y,hy,rfl⟩,hgy⟩
        refine ⟨y,?_,rfl⟩
        rw [he]
        exact ⟨hy,by simpa only [Set.mem_ofPred_eq,hg] using hgy⟩

end MaxLatticeFree.Geometry.Proof
-- End SubtypeFacet

-- Begin NativePolyhedron

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma subtype_image_preimage_of_subset (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ (W : Set _)) :
    Subtype.val '' ((Subtype.val : W → _) ⁻¹' S)=S := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx; exact ⟨⟨x,hS hx⟩,hx,rfl⟩

lemma nativePolyhedron_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ (W : Set _)) :
    IsPolyhedronIn W S ↔ Polyhedral ((Subtype.val : W → _) ⁻¹' S) := by
  constructor
  · rintro ⟨t,a,b,he⟩
    refine ⟨t,(fun i => (innerSL ℝ (a i)).toLinearMap.comp W.subtype),b,?_⟩
    ext x
    simp only [he,mem_preimage,mem_inter_iff,SetLike.mem_coe,x.property,true_and]
    rfl
  · rintro ⟨t,g,b,he⟩
    let a : Fin t → W := fun i => (InnerProductSpace.toDual ℝ W).symm (g i).toContinuousLinearMap
    have ha : ∀ i (x : W), inner ℝ (a i : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))=g i x := by
      intro i x
      change inner ℝ (a i) x=g i x
      simp [a]
    refine ⟨t,(fun i => (a i : EuclideanSpace ℝ (Fin n))),b,?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨hS hx,?_⟩
      let y : W := ⟨x,hS hx⟩
      have hy : y∈(Subtype.val : W → _) ⁻¹' S := hx
      rw [he] at hy
      intro i
      change inner ℝ (a i : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))≤b i
      rw [ha]
      exact hy i
    · rintro ⟨hxW,hx⟩
      let y : W := ⟨x,hxW⟩
      have hy : y∈polyBody g b := by
        intro i
        rw [← ha i y]
        exact hx i
      rw [← he] at hy
      exact hy

lemma nativeFullDim_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ (W : Set _)) (hc : Convex ℝ S) :
    affDim S=(Module.finrank ℝ W : ℤ) ↔
      (interior ((Subtype.val : W → _) ⁻¹' S)).Nonempty := by
  let P : Set W := Subtype.val ⁻¹' S
  have himg : Subtype.val '' P=S := subtype_image_preimage_of_subset W S hS
  have hconv : Convex ℝ P := hc.linear_preimage W.subtype
  have hrank : Module.finrank ℝ (affineSpan ℝ S).direction = Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [← himg]
    exact direction_rank_subtype_image W P
  constructor
  · intro hd
    have hne : S.Nonempty := by
      by_contra hn
      simp only [affDim,if_neg hn] at hd
      omega
    have hPne : P.Nonempty := image_nonempty.mp (himg.symm ▸ hne)
    have hdNat : Module.finrank ℝ (affineSpan ℝ P).direction=Module.finrank ℝ W := by
      simp only [affDim,if_pos hne] at hd
      rw [hrank] at hd
      omega
    have hdir : (affineSpan ℝ P).direction=⊤ := Submodule.eq_top_of_finrank_eq hdNat
    exact hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
      ((AffineSubspace.direction_eq_top_iff_of_nonempty (hPne.affineSpan ℝ)).mp hdir)
  · intro hi
    have hPne : P.Nonempty := hi.mono interior_subset
    have hne : S.Nonempty := himg ▸ hPne.image Subtype.val
    simp only [affDim,if_pos hne]
    rw [hrank,hconv.interior_nonempty_iff_affineSpan_eq_top.mp hi,
      AffineSubspace.direction_top,finrank_top]

end MaxLatticeFree.Geometry.Proof
-- End NativePolyhedron

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

-- Begin FreeEquiv

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma free_preimage_equiv_iff (e : E ≃L[ℝ] F) (Γ : AddSubgroup F) (S : Set F) :
    Free (Γ.comap e.toLinearMap.toAddMonoidHom) (e ⁻¹' S) ↔ Free Γ S := by
  have hInt : e ⁻¹' interior S=interior (e ⁻¹' S) := e.toHomeomorph.preimage_interior S
  constructor
  · rintro ⟨hc,hf⟩
    have himage : e '' (e ⁻¹' S)=S := image_preimage_eq S e.surjective
    refine ⟨?_,?_⟩
    · rw [← himage]
      exact hc.linear_image e.toLinearMap
    · intro y hy hyΓ
      have hx : e.symm y∈interior (e ⁻¹' S) := by
        rw [← hInt]
        simpa using hy
      exact hf (e.symm y) hx (by simpa using hyΓ)
  · rintro ⟨hc,hf⟩
    refine ⟨hc.linear_preimage e.toLinearMap,?_⟩
    intro x hx hxΓ
    rw [← hInt] at hx
    exact hf (e x) hx hxΓ

lemma maxFree_preimage_equiv_iff (e : E ≃L[ℝ] F) (Γ : AddSubgroup F) (S : Set F) :
    MaxFree (Γ.comap e.toLinearMap.toAddMonoidHom) (e ⁻¹' S) ↔ MaxFree Γ S := by
  constructor
  · rintro ⟨hf,hm⟩
    refine ⟨(free_preimage_equiv_iff e Γ S).mp hf,?_⟩
    intro K hK hSK
    have hh := hm (e ⁻¹' K) ((free_preimage_equiv_iff e Γ K).mpr hK) (preimage_mono hSK)
    exact e.surjective.preimage_injective hh
  · rintro ⟨hf,hm⟩
    refine ⟨(free_preimage_equiv_iff e Γ S).mpr hf,?_⟩
    intro K hK hSK
    have hpre : e ⁻¹' (e '' K)=K := preimage_image_eq K e.injective
    have hfK : Free Γ (e '' K) :=
      (free_preimage_equiv_iff e Γ (e '' K)).mp (hpre.symm ▸ hK)
    have hsub : S ⊆ e '' K := by
      intro y hy
      exact ⟨e.symm y,hSK (by simpa using hy),e.apply_symm_apply y⟩
    have he := hm (e '' K) hfK hsub
    rw [← hpre,he]

end MaxLatticeFree.Geometry.Proof
-- End FreeEquiv

-- Begin NativeNested

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma native_nested_span (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V≤W) :
    Submodule.span ℝ
      ((Λ.comap W.subtype.toAddMonoidHom).comap (V.comap W.subtype).subtype.toAddMonoidHom :
        Set (V.comap W.subtype))=⊤ := by
  let Γ := Λ.comap W.subtype.toAddMonoidHom
  let L := V.comap W.subtype
  have hΓ : (Γ : Set W) ⊆ (L : Set W) := fun x hx => native_lattice_subset hΛ hx
  apply subtype_span_top Γ L
  rw [inter_eq_left.mpr hΓ]
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span]
  have he : W.subtype '' (Γ : Set W)=(Λ : Set _) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx
      exact ⟨⟨x,hVW (native_lattice_subset hΛ hx)⟩,hx,rfl⟩
  rw [he,native_lattice_span hΛ]
  change V=(V.comap W.subtype).map W.subtype
  rw [Submodule.map_comap_subtype,inf_eq_right.mpr hVW]

lemma native_section_maxFree_iff (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hVW : V≤W)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    let U : Submodule ℝ W := V.comap W.subtype
    IsMaxLambdaFree Λ V (S ∩ (V : Set _)) ↔
      @MaxFree U U.normedAddCommGroup (Submodule.innerProductSpace U) ((Λ.comap W.subtype.toAddMonoidHom).comap U.subtype.toAddMonoidHom)
        ((Subtype.val : U → W) ⁻¹' ((Subtype.val : W → _) ⁻¹' S)) := by
  dsimp only
  let e : (V.comap W.subtype) ≃L[ℝ] V :=
    (Submodule.comapSubtypeEquivOfLe hVW).toContinuousLinearEquiv
  rw [nativeMaxFree_iff Λ V (S ∩ (V : Set _)) inter_subset_right]
  have he : (Subtype.val : V → _) ⁻¹' (S ∩ (V : Set _))=(Subtype.val : V → _) ⁻¹' S := by
    ext x; simp
  rw [he]
  have hh := (maxFree_preimage_equiv_iff (E := (V.comap W.subtype : Submodule ℝ W)) e (Λ.comap V.subtype.toAddMonoidHom)
    ((Subtype.val : V → _) ⁻¹' S)).symm
  exact hh

lemma nativeFacet_subtype_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S F : Set (EuclideanSpace ℝ (Fin n))) (hS : S⊆(W : Set _)) (hF : F⊆(W : Set _)) :
    IsFacet S F ↔ GFacet ((Subtype.val : W → _) ⁻¹' S) ((Subtype.val : W → _) ⁻¹' F) := by
  rw [nativeFacet_iff_gFacet,← subtype_image_preimage_of_subset W S hS,
    ← subtype_image_preimage_of_subset W F hF,gFacet_subtype_image_iff]
  simp only [Set.preimage_image_eq _ Subtype.val_injective]

lemma nested_subtype_image_preimage (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hVW : V≤W) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S⊆(V : Set _)) :
    (Subtype.val : W → _) '' ((Subtype.val : V.comap W.subtype → W) ''
      ((Subtype.val : V.comap W.subtype → W) ⁻¹' ((Subtype.val : W → _) ⁻¹' S)))=S := by
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩; exact hy
  · intro hx
    let y : V.comap W.subtype := ⟨⟨x,hVW (hS hx)⟩,hS hx⟩
    exact ⟨y,⟨y,hx,rfl⟩,rfl⟩

lemma nativeFacet_nested_iff (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hVW : V≤W) (S F : Set (EuclideanSpace ℝ (Fin n))) (hS : S⊆(V : Set _)) (hF : F⊆(V : Set _)) :
    IsFacet S F ↔ GFacet
      ((Subtype.val : V.comap W.subtype → W) ⁻¹' ((Subtype.val : W → _) ⁻¹' S))
      ((Subtype.val : V.comap W.subtype → W) ⁻¹' ((Subtype.val : W → _) ⁻¹' F)) := by
  rw [nativeFacet_iff_gFacet,← nested_subtype_image_preimage V W hVW S hS,
    ← nested_subtype_image_preimage V W hVW F hF,
    gFacet_subtype_image_iff,gFacet_subtype_image_iff]
  simp only [Set.preimage_image_eq _ Subtype.val_injective]

end MaxLatticeFree.Geometry.Proof
-- End NativeNested

-- Begin FreeGeometry

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem MaxFree.isClosed {Γ : AddSubgroup E} {S : Set E} (h : MaxFree Γ S)
    (hi : (interior S).Nonempty) : IsClosed S := by
  have he : closure S = S := h.2 _ ⟨h.1.1.closure, by
    rw [h.1.1.interior_closure_eq_interior_of_nonempty_interior hi]
    exact h.1.2⟩ subset_closure
  exact he ▸ isClosed_closure

theorem interior_add_submodule {S : Set E} (hs : Convex ℝ S)
    (hi : (interior S).Nonempty) (L : Submodule ℝ E) :
    interior (S + (L : Set E)) = interior S + (L : Set E) := by
  apply Subset.antisymm _ subset_interior_add_left
  intro y hy
  obtain ⟨x,hx⟩ := hi
  have he := AffineMap.lineMap_apply_one (k := ℝ) x y
  obtain ⟨t,ht,hz⟩ := AffineMap.lineMap_continuous.tendsto' _ _ he |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp hy) |>.exists_gt
  obtain ⟨s,hs',l,hl,heq⟩ := hz
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hti : 0 < t⁻¹ := inv_pos.mpr ht0
  have htil : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
  refine ⟨(1-t⁻¹) • x + t⁻¹ • s,
    hs.combo_interior_closure_mem_interior hx (subset_closure hs') (by linarith)
      hti.le (by ring),t⁻¹ • l,L.smul_mem _ hl,?_⟩
  have hz : s+l=(1-t) • x+t • y := by
    change s+l=AffineMap.lineMap x y t at heq
    rw [heq]
    simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add]
    module
  calc
    ((1-t⁻¹) • x+t⁻¹ • s)+t⁻¹ • l = (1-t⁻¹) • x+t⁻¹ • (s+l) := by module
    _ = y := by
      rw [hz,smul_add,smul_smul,smul_smul,inv_mul_cancel₀ ht0.ne',one_smul]
      have hc : t⁻¹*(1-t)=t⁻¹-1 := by field_simp
      rw [hc]
      module

 theorem Free.add_closure_submodule {Γ : AddSubgroup E} {S : Set E}
    (h : Free Γ S) (hi : (interior S).Nonempty) (L : Submodule ℝ E)
    (hL : (L : Set E) ⊆ closure (Γ : Set E)) : Free Γ (S+(L:Set E)) := by
  refine ⟨h.1.add L.convex,?_⟩
  rw [interior_add_submodule h.1 hi L]
  rintro y ⟨s,hs,l,hl,rfl⟩ hy
  have hopen : IsOpen {z : E | s+l-z∈interior S} := isOpen_interior.preimage (by fun_prop)
  have hmem : l∈{z : E | s+l-z∈interior S} := by simpa
  obtain ⟨g,hgg,hg⟩ := (mem_closure_iff_nhds.mp (hL hl)) _ (hopen.mem_nhds hmem)
  exact h.2 (s+l-g) hgg (Γ.sub_mem hy hg)

end MaxLatticeFree.Geometry.Proof
-- End FreeGeometry

-- Begin RecessionBasic

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Recedes (S : Set E) (r : E) : Prop := ∀x∈S,∀t:ℝ,0≤t→x+t • r∈S

def lineality (S : Set E) : Submodule ℝ E where
  carrier := {r | ∀x∈S,∀t:ℝ,x+t • r∈S}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs x hx t
    simpa [smul_add,add_assoc] using hs (x+t • r) (hr x hx t) t
  smul_mem' := by
    intro a r hr x hx t
    simpa [smul_smul] using hr x hx (t*a)

lemma lineality_recedes (S : Set E) {r : E} (hr : r∈lineality S) : Recedes S r :=
  fun x hx t _ => hr x hx t

lemma add_lineality (S : Set E) : S + (lineality S:Set E)=S := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,r,hr,rfl⟩
    simpa using hr y hy 1
  · intro x hx
    exact ⟨x,hx,0,(lineality S).zero_mem,by simp⟩

lemma recedes_interior {S : Set E} {r : E} (hr : Recedes S r)
    {x : E} (hx : x∈interior S) {t : ℝ} (ht : 0≤t) : x+t • r∈interior S := by
  have hsub : (fun y:E=>y+t • r) '' S ⊆ S := by rintro _ ⟨y,hy,rfl⟩; exact hr y hy t ht
  apply interior_mono hsub
  exact (isOpenMap_add_right (t • r)).image_interior_subset S ⟨x,hx,rfl⟩

end MaxLatticeFree.Geometry.Proof
-- End RecessionBasic

-- Begin OrthogonalSlice

open Set
open scoped Pointwise Topology
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma projection_surjective (Q : Submodule ℝ E) : Function.Surjective Q.orthogonalProjectionOnto := by
  intro q
  exact ⟨q,Q.orthogonalProjectionOnto_mem_subspace_eq_self q⟩

lemma projection_open (Q : Submodule ℝ E) : IsOpenMap Q.orthogonalProjectionOnto :=
  Q.orthogonalProjectionOnto.isOpenMap (projection_surjective Q)

lemma orthogonal_slice_eq (S : Set E) :
    S=(lineality S)ᗮ.orthogonalProjectionOnto ⁻¹' ((Subtype.val : (lineality S)ᗮ → E) ⁻¹' S) := by
  let L := lineality S
  have hl (x:E) : x-((Lᗮ.orthogonalProjectionOnto x):E)∈L := by
    have h := (Lᗮ).sub_starProjection_mem_orthogonal x
    change x-Lᗮ.starProjection x∈L
    simpa only [Submodule.orthogonal_orthogonal] using h
  ext x
  change x∈S ↔ ((Lᗮ.orthogonalProjectionOnto x):E)∈S
  constructor
  · intro hx
    have h := hl x
    have hh := h x hx (-1)
    convert hh using 1; module
  · intro hx
    have h := hl x
    have hh := h _ hx 1
    convert hh using 1; module

lemma projection_preimage_interior (Q : Submodule ℝ E) (P : Set Q) :
    interior (Q.orthogonalProjectionOnto ⁻¹' P)=Q.orthogonalProjectionOnto ⁻¹' interior P := by
  exact (projection_open Q).preimage_interior_eq_interior_preimage Q.orthogonalProjectionOnto.continuous P |>.symm

lemma slice_interior_nonempty {S : Set E} (hi : (interior S).Nonempty) :
    (interior ((Subtype.val : (lineality S)ᗮ → E) ⁻¹' S)).Nonempty := by
  obtain ⟨x,hx⟩ := hi
  refine ⟨(lineality S)ᗮ.orthogonalProjectionOnto x,?_⟩
  rw [orthogonal_slice_eq S,projection_preimage_interior] at hx
  exact hx

lemma slice_maxFree (Γ : AddSubgroup E) {S : Set E} (h : MaxFree Γ S) :
    MaxFree (Γ.map ((lineality S)ᗮ.orthogonalProjectionOnto.toLinearMap.toAddMonoidHom))
      ((Subtype.val : (lineality S)ᗮ → E) ⁻¹' S) := by
  let Q := (lineality S)ᗮ
  let P : Set Q := Subtype.val ⁻¹' S
  let π := Q.orthogonalProjectionOnto
  have hS : S=π ⁻¹' P := orthogonal_slice_eq S
  refine ⟨⟨h.1.1.linear_preimage Q.subtype,?_⟩,?_⟩
  · intro y hy hγ
    obtain ⟨x,hx,he⟩ := hγ
    have hin : x∈interior S := by
      rw [hS,projection_preimage_interior]
      change π x∈interior P
      change π x=y at he
      rw [he]
      exact hy
    exact h.1.2 x hin hx
  · intro K hK hPK
    have hfree : Free Γ (π ⁻¹' K) := by
      refine ⟨hK.1.linear_preimage π.toLinearMap,?_⟩
      intro x hx hγ
      rw [projection_preimage_interior] at hx
      exact hK.2 _ hx (AddSubgroup.mem_map.mpr ⟨x,hγ,rfl⟩)
    have he := h.2 _ hfree (by rw [hS]; exact preimage_mono hPK)
    apply (preimage_injective.mpr (projection_surjective Q))
    exact he.trans hS

end MaxLatticeFree.Geometry.Proof
-- End OrthogonalSlice

-- Begin TorusApproximation

open Set Filter
open scoped BigOperators Topology
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma fractional_sequence_cauchy {I : Type*} [Fintype I] (a : I → E) (c : I → ℝ) (T : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun n=>∑i,Int.fract ((φ n:ℝ)*T*c i) • a i) := by
  let f : (I → ℝ) → E := fun x=>∑i,x i • a i
  let u : ℕ → E := fun n=>f (fun i=>Int.fract ((n:ℝ)*T*c i))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hu (n : ℕ) : u n∈f '' Icc (0:I→ℝ) 1 := by
    refine ⟨_,⟨?_,?_⟩,rfl⟩
    · intro i; exact Int.fract_nonneg _
    · intro i; exact (Int.fract_lt_one _).le
  obtain ⟨y,_,φ,hφ,hlim⟩ := (isCompact_Icc.image hf).tendsto_subseq hu
  exact ⟨φ,hφ,hlim.cauchySeq⟩

lemma fractional_difference {I : Type*} [Fintype I] (a : I → E) (c : I → ℝ) (p q T : ℝ) :
    (∑i,Int.fract (p*T*c i) • a i)-(∑i,Int.fract (q*T*c i) • a i)=
      ((p-q)*T) • (∑i,c i • a i)-(∑i,(⌊p*T*c i⌋-⌊q*T*c i⌋) • a i) := by
  simp only [Finset.smul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.cast_smul_eq_zsmul (R := ℝ)]
  simp only [Int.fract,Int.cast_sub,smul_smul,sub_smul]
  module

lemma finite_ray_approximation {I : Type*} [Fintype I] (Γ : AddSubgroup E)
    (a : I → E) (ha : ∀i,a i∈Γ) (c : I → ℝ) (ε lam : ℝ) (hε : 0<ε) (hlam : 0≤lam) :
    ∃ t : ℝ, lam≤t ∧ ∃g∈Γ, ‖t • (∑i,c i • a i)-g‖<ε := by
  classical
  let T := lam+1
  let u : ℕ → E := fun n=>∑i,Int.fract ((n:ℝ)*T*c i) • a i
  obtain ⟨φ,hφ,hlim⟩ := fractional_sequence_cauchy a c T
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hlim ε hε
  have hdist := hN N (le_refl _) (N+1) (by omega)
  let t := ((φ (N+1):ℝ)-(φ N:ℝ))*T
  let g := ∑i, (⌊(φ (N+1):ℝ)*T*c i⌋-⌊(φ N:ℝ)*T*c i⌋) • a i
  have ht : lam≤t := by
    have hφ' : (φ N:ℝ)+1≤(φ (N+1):ℝ) := by exact_mod_cast hφ (Nat.lt_succ_self N)
    dsimp [t,T]
    nlinarith
  have hg : g∈Γ := Γ.sum_mem (fun i _=>Γ.zsmul_mem (ha i) _)
  refine ⟨t,ht,g,hg,?_⟩
  have he : u (φ (N+1))-u (φ N)=t • (∑i,c i • a i)-g :=
    fractional_difference a c _ _ T
  rw [← he]
  simpa [Function.comp_def,dist_eq_norm,norm_sub_rev] using hdist

lemma ray_approximation [FiniteDimensional ℝ E] (Γ : AddSubgroup E)
    (hspan : Submodule.span ℝ (Γ:Set E)=⊤) (r : E)
    (ε lam : ℝ) (hε : 0<ε) (hlam : 0≤lam) :
    ∃t:ℝ,lam≤t ∧ ∃g∈Γ,‖t • r-g‖<ε := by
  classical
  let b := Module.Basis.ofSpan (show (⊤:Submodule ℝ E)≤Submodule.span ℝ (Γ:Set E) by rw [hspan])
  let := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ E)
  have hb : ∀i,b i∈Γ := fun i=>Module.Basis.ofSpan_subset _ ⟨i,rfl⟩
  have he : ∑i,(b.repr r i) • b i=r := b.sum_repr r
  simpa only [he] using finite_ray_approximation Γ b hb (fun i=>b.repr r i) ε lam hε hlam

end MaxLatticeFree.Geometry.Proof
-- End TorusApproximation

-- Begin RecessionFree

open Set Metric
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma Free.add_recession_line {Γ : AddSubgroup E} {S : Set E}
    (hspan : Submodule.span ℝ (Γ:Set E)=⊤) (h : Free Γ S)
    (hi : (interior S).Nonempty) {r : E} (hr : Recedes S r) :
    Free Γ (S+(Submodule.span ℝ {r}:Set E)) := by
  refine ⟨h.1.add (Submodule.span ℝ {r}).convex,?_⟩
  rw [interior_add_submodule h.1 hi]
  rintro y ⟨s,hs,l,hl,rfl⟩ hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hl
  by_cases ha : 0≤a
  · exact h.2 _ (recedes_interior hr hs ha) hy
  have han : 0≤-a := by linarith
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior s hs
  obtain ⟨t,ht,g,hg,hclose⟩ := ray_approximation Γ hspan r ε (-a) hε han
  let q := (s+a • r)+g-(t+a) • r
  have hq : q∈interior S := by
    apply hball
    have he : q-s=g-t • r := by dsimp [q]; module
    simpa [mem_ball,dist_eq_norm,he,norm_sub_rev] using hclose
  have hsum : 0≤t+a := by linarith
  have he : q+(t+a) • r=(s+a • r)+g := by dsimp [q]; abel
  exact h.2 _ (he ▸ recedes_interior hr hq hsum) (Γ.add_mem hy hg)

lemma MaxFree.recedes_mem_lineality {Γ : AddSubgroup E} {S : Set E}
    (hspan : Submodule.span ℝ (Γ:Set E)=⊤) (h : MaxFree Γ S)
    (hi : (interior S).Nonempty) {r : E} (hr : Recedes S r) : r∈lineality S := by
  have he : S+(Submodule.span ℝ {r}:Set E)=S := h.2 _
    (h.1.add_recession_line hspan hi hr) (by
      intro x hx; exact ⟨x,hx,0,(Submodule.span ℝ {r}).zero_mem,by simp⟩)
  intro x hx t
  rw [← he]
  exact ⟨x,hx,t • r,Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),rfl⟩

end MaxLatticeFree.Geometry.Proof
-- End RecessionFree

-- Begin RecessionBounded

open Set Filter Metric
open scoped Topology
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma recedes_of_normalized_limit {S : Set E} (hc : IsClosed S) (hv : Convex ℝ S)
    (x : ℕ → E) (hx : ∀n,x n∈S)
    (hn : Tendsto (fun n=>‖x n‖) atTop atTop)
    (u : E) (hu : Tendsto (fun n=>‖x n‖⁻¹ • x n) atTop (𝓝 u)) : Recedes S u := by
  intro y hy t ht
  have hi : Tendsto (fun n=>‖x n‖⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero.comp hn
  have hl : Tendsto (fun n=>y-(t*‖x n‖⁻¹) • y+t • (‖x n‖⁻¹ • x n)) atTop (𝓝 (y+t • u)) := by
    simpa using (tendsto_const_nhds.sub ((tendsto_const_nhds.mul hi).smul tendsto_const_nhds)).add
      (tendsto_const_nhds.smul hu)
  apply hc.mem_of_tendsto hl
  filter_upwards [hn.eventually (eventually_ge_atTop (max t 1))] with n hlarge
  have hpos : 0<‖x n‖ := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hlarge)
  have hle : t*‖x n‖⁻¹≤1 := by rw [← div_eq_mul_inv,div_le_one hpos]; exact (le_max_left _ _).trans hlarge
  have hnon : 0≤t*‖x n‖⁻¹ := mul_nonneg ht (inv_nonneg.mpr (norm_nonneg _))
  have hm := hv hy (hx n) (sub_nonneg.mpr hle) hnon (show 1-t*‖x n‖⁻¹+t*‖x n‖⁻¹=1 by ring)
  convert hm using 1; module

lemma exists_unit_recession_of_unbounded [FiniteDimensional ℝ E] {S : Set E}
    (hc : IsClosed S) (hv : Convex ℝ S) (hb : ¬Bornology.IsBounded S) :
    ∃u:E, ‖u‖ = 1 ∧ Recedes S u := by
  classical
  have hx : ∀n:ℕ,∃x∈S,(n:ℝ)+1<‖x‖ := by
    intro n
    by_contra hn
    push Not at hn
    exact hb (isBounded_iff_forall_norm_le.mpr ⟨(n:ℝ)+1,hn⟩)
  choose x hx hxn using hx
  have hn : Tendsto (fun n=>‖x n‖) atTop atTop :=
    tendsto_atTop_mono (fun n=>(hxn n).le) (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hne (n:ℕ) : x n≠0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (lt_trans (by positivity : (0:ℝ)<(n:ℝ)+1) (hxn n))
  have hunit (n:ℕ) : ‖x n‖⁻¹ • x n∈sphere (0:E) 1 := by
    simp [norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne n))]
  obtain ⟨u,hum,φ,hφ,hlim⟩ := (isCompact_sphere (0:E) 1).tendsto_subseq hunit
  refine ⟨u,by simpa [mem_sphere,dist_eq_norm] using hum,?_⟩
  exact recedes_of_normalized_limit hc hv (x ∘ φ) (fun n=>hx _) (hn.comp hφ.tendsto_atTop) u hlim

lemma bounded_of_recession_zero [FiniteDimensional ℝ E] {S : Set E}
    (hc : IsClosed S) (hv : Convex ℝ S) (hz : ∀ r, Recedes S r → r = 0) : Bornology.IsBounded S := by
  by_contra hb
  obtain ⟨u,hu,hr⟩ := exists_unit_recession_of_unbounded hc hv hb
  simp [hz u hr] at hu

end MaxLatticeFree.Geometry.Proof
-- End RecessionBounded

-- Begin GroupClosureLine

open Set Filter Metric
open scoped Topology
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma line_mem_closure_of_small_sequence (Γ : AddSubgroup E) (g : ℕ → E)
    (hg : ∀n,g n∈Γ) (hne : ∀n,g n≠0) (hzero : Tendsto (fun n=>‖g n‖) atTop (𝓝 0))
    (u : E) (hdir : Tendsto (fun n=>‖g n‖⁻¹ • g n) atTop (𝓝 u)) (t : ℝ) :
    t • u∈closure (Γ:Set E) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0<ε/(2*(|t|+1)) := div_pos hε (by positivity)
  have hd := (Metric.tendsto_atTop.mp hdir) _ hδ
  obtain ⟨N,hN⟩ := hd
  have hz := hzero.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨n,hn,hgn⟩ := (eventually_ge_atTop N).and hz |>.exists
  let z : ℤ := ⌊t/‖g n‖⌋
  refine ⟨z • g n,Γ.zsmul_mem (hg n) z,?_⟩
  have hnorm : 0<‖g n‖ := norm_pos_iff.mpr (hne n)
  have he : z • g n-t • u = t • (‖g n‖⁻¹ • g n-u)-Int.fract (t/‖g n‖) • g n := by
    dsimp [z]
    rw [Int.fract]
    simp only [smul_sub,smul_smul,sub_smul,Int.cast_smul_eq_zsmul,div_eq_mul_inv]
    module
  have hbound : ‖z • g n-t • u‖ ≤ |t| * ‖‖g n‖⁻¹ • g n-u‖+‖g n‖ := by
    rw [he]
    apply (norm_sub_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg (t/‖g n‖))]
    exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg (g n)) (Int.fract_lt_one (t/‖g n‖)).le)
  have hd' : ‖‖g n‖⁻¹ • g n-u‖ < ε/(2*(|t|+1)) := by simpa [dist_eq_norm] using hN n hn
  have hc : |t| * (ε/(2*(|t|+1))) < ε/2 := by
    have hh : 0 < |t|+1 := by positivity
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith [abs_nonneg t]
  have hmul := mul_le_mul_of_nonneg_left hd'.le (abs_nonneg t)
  rw [dist_eq_norm,norm_sub_rev]
  exact hbound.trans_lt (by linarith)

lemma nondiscrete_group_closure_line [FiniteDimensional ℝ E] (Γ : AddSubgroup E)
    (h : ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ t : ℝ, t • u ∈ closure (Γ:Set E) := by
  classical
  have hg : ∀n:ℕ,∃g:E,g∈Γ ∧ ‖g‖<1/((n:ℝ)+1) ∧ g≠0 := by
    intro n
    by_contra hn
    push Not at hn
    exact h ⟨1/((n:ℝ)+1),by positivity,fun g hgm hgn=>hn g hgm hgn⟩
  choose g hgm hgn hgne using hg
  have hz : Tendsto (fun n=>‖g n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n=>norm_nonneg _) (fun n=>(hgn n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hu (n:ℕ) : ‖g n‖⁻¹ • g n∈sphere (0:E) 1 := by
    simp [norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne n))]
  obtain ⟨u,hum,φ,hφ,hlim⟩ := (isCompact_sphere (0:E) 1).tendsto_subseq hu
  refine ⟨u,by simpa [mem_sphere,dist_eq_norm] using hum,?_⟩
  intro t
  exact line_mem_closure_of_small_sequence Γ (g ∘ φ) (fun n=>hgm _) (fun n=>hgne _)
    (hz.comp hφ.tendsto_atTop) u hlim t

end MaxLatticeFree.Geometry.Proof
-- End GroupClosureLine

-- Begin BoundedFreeDiscrete

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma bounded_maxFree_discrete (Γ : AddSubgroup E) {S : Set E}
    (hS : MaxFree Γ S) (hi : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0 := by
  by_contra h
  obtain ⟨u,hu,hline⟩ := nondiscrete_group_closure_line Γ h
  have hL : (Submodule.span ℝ {u}:Set E) ⊆ closure (Γ:Set E) := by
    intro x hx
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact hline t
  have he : S+(Submodule.span ℝ {u}:Set E)=S := hS.2 _
    (hS.1.add_closure_submodule hi _ hL) (by
      intro x hx; exact ⟨x,hx,0,(Submodule.span ℝ {u}).zero_mem,by simp⟩)
  obtain ⟨x,hx⟩ := hi
  have hxS := interior_subset hx
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  let t := R+‖x‖+1
  have ht : 0<t := by have := hR x hxS; dsimp [t]; nlinarith [norm_nonneg x]
  have hmem : x+t • u∈S := by
    rw [← he]
    exact ⟨x,hxS,t • u,Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),rfl⟩
  have hn : ‖t • u‖≤R+‖x‖ := by
    calc
      ‖t • u‖ = ‖(x+t • u)-x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x+t • u‖+‖x‖ := norm_sub_le _ _
      _ ≤ R+‖x‖ := add_le_add (hR _ hmem) le_rfl
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hu,mul_one] at hn
  dsimp [t] at hn
  linarith

end MaxLatticeFree.Geometry.Proof
-- End BoundedFreeDiscrete

-- Begin BoundedQuotient

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma orthogonal_slice_bounded (Γ : AddSubgroup E) (hspan : Submodule.span ℝ (Γ:Set E)=⊤)
    {S : Set E} (hS : MaxFree Γ S) (hi : (interior S).Nonempty) :
    Bornology.IsBounded ((Subtype.val : (lineality S)ᗮ → E) ⁻¹' S) := by
  let L := lineality S
  let Q := Lᗮ
  let P : Set Q := Subtype.val ⁻¹' S
  have hc : IsClosed P := (hS.isClosed hi).preimage continuous_subtype_val
  have hv : Convex ℝ P := hS.1.1.linear_preimage Q.subtype
  apply bounded_of_recession_zero hc hv
  intro r hr
  have hre : Recedes S (r:E) := by
    intro x hx t ht
    rw [orthogonal_slice_eq S] at hx ⊢
    change Q.orthogonalProjectionOnto (x+t • (r:E))∈P
    simpa only [map_add,map_smul,Q.orthogonalProjectionOnto_mem_subspace_eq_self r] using
      hr (Q.orthogonalProjectionOnto x) hx t ht
  have hrL : (r:E)∈L := hS.recedes_mem_lineality hspan hi hre
  have hzero : (r:E)=0 := inner_self_eq_zero.mp (L.inner_right_of_mem_orthogonal hrL r.property)
  exact Subtype.ext hzero

lemma bounded_quotient (Γ : AddSubgroup E) (hspan : Submodule.span ℝ (Γ:Set E)=⊤)
    {S : Set E} (hS : MaxFree Γ S) (hi : (interior S).Nonempty) :
    ∃L:Submodule ℝ E,
      let Q := Lᗮ
      let P : Set Q := (Subtype.val : Q → E) ⁻¹' S
      let Γ' := Γ.map Q.orthogonalProjectionOnto.toLinearMap.toAddMonoidHom
      IsCompact P ∧ (interior P).Nonempty ∧ MaxFree Γ' P ∧
        S=Q.orthogonalProjectionOnto ⁻¹' P ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ', ‖g‖ < ε → g = 0 := by
  refine ⟨lineality S,?_⟩
  dsimp only
  have hb := orthogonal_slice_bounded Γ hspan hS hi
  have hc := (hS.isClosed hi).preimage (continuous_subtype_val (p := fun x=>x∈(lineality S)ᗮ))
  have hp := slice_maxFree Γ hS
  have hpi := slice_interior_nonempty hi
  exact ⟨Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc,hb⟩,hpi,hp,orthogonal_slice_eq S,bounded_maxFree_discrete _ hp hpi hb⟩

end MaxLatticeFree.Geometry.Proof
-- End BoundedQuotient

-- Begin SupportingFunctional

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma supporting_functional {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) {z : E} (hz : z ∉ interior S) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ x ∈ S, f x ≤ f z) := by
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hS.interior isOpen_interior hz
  have hn : f ≠ 0 := by
    intro he
    obtain ⟨x,hx⟩ := hint
    have hh := hf x hx
    simp [he] at hh
  refine ⟨f,hn,?_⟩
  have hcl : closure (interior S) ⊆ {x | f x ≤ f z} :=
    closure_minimal (fun x hx => (hf x hx).le) (isClosed_le f.continuous continuous_const)
  rw [hS.closure_interior_eq_closure_of_nonempty_interior hint] at hcl
  exact fun x hx => hcl (subset_closure hx)

end MaxLatticeFree.Geometry.Proof
-- End SupportingFunctional

-- Begin BoundedPolyhedral

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

lemma bounded_maxFree_polyhedral (Γ : AddSubgroup E) {S : Set E}
    (hΓ : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0)
    (hS : MaxFree Γ S) (hint : (interior S).Nonempty)
    (hbound : Bornology.IsBounded S) : Polyhedral S := by
  classical
  obtain ⟨K,hpoly,hcomp,hsub⟩ := exists_compact_outer_poly hbound
  let Z := K ∩ (Γ : Set E)
  have hfin : Z.Finite := finite_compact_inter_group Γ hΓ hcomp
  let : Fintype Z := hfin.fintype
  have hsup : ∀ z : Z, ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ x ∈ S, f x ≤ f z := by
    intro z
    apply supporting_functional hS.1.1 hint
    intro hz
    exact hS.1.2 z hz z.property.2
  choose f hf hfs using hsup
  let a : Z → E →ₗ[ℝ] ℝ := fun z => (f z).toLinearMap
  let b : Z → ℝ := fun z => f z z
  let Q := K ∩ polyBody a b
  have hSQ : S ⊆ Q := by
    intro x hx
    exact ⟨interior_subset (hsub hx),fun z => hfs z x hx⟩
  have hQfree : Free Γ Q := by
    refine ⟨?_,?_⟩
    · obtain ⟨t,c,d,hK⟩ := hpoly
      rw [show Q = K ∩ polyBody a b from rfl,hK]
      exact (polyBody_convex c d).inter (polyBody_convex a b)
    · intro x hx hxΓ
      have hxK : x ∈ K := (interior_subset hx).1
      let z : Z := ⟨x,hxK,hxΓ⟩
      have hxP : x ∈ interior (polyBody a b) := interior_mono inter_subset_right hx
      have ha : ∀ z, a z ≠ 0 := by
        intro z he
        apply hf z
        ext y
        exact congrArg (fun l : E →ₗ[ℝ] ℝ => l y) he
      have hlt := interior_polyBody_strict a b ha hxP z
      exact (lt_irrefl (f z x)) hlt
  have hQS : Q = S := hS.2 Q hQfree hSQ
  rw [← hQS]
  exact polyhedral_inter hpoly (polyhedral_polyBody a b)

end MaxLatticeFree.Geometry.Proof
-- End BoundedPolyhedral

-- Begin PolyRecession

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*}

lemma polyBody_recession_zero (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hne : (polyBody a b).Nonempty) (hbounded : Bornology.IsBounded (polyBody a b)) :
    ∀ d, (∀ i, a i d ≤ 0) → d = 0 := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hbounded
  intro d hd
  by_contra hn
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hn
  let t : ℝ := (|R|+‖p‖+1)/‖d‖
  have ht : 0 < t := div_pos (by positivity) hnorm
  have he : t * ‖d‖ = |R|+‖p‖+1 := div_mul_cancel₀ _ hnorm.ne'
  have hmem : p+t • d ∈ polyBody a b := by
    intro i
    simp only [map_add,map_smul,smul_eq_mul]
    have hh := mul_nonpos_of_nonneg_of_nonpos ht.le (hd i)
    linarith [hp i]
  have hb := hR _ hmem
  have htri : ‖t • d‖ ≤ ‖p+t • d‖+‖p‖ := by
    calc
      ‖t • d‖ = ‖(p+t • d)-p‖ := by congr 1; abel
      _ ≤ ‖p+t • d‖+‖p‖ := norm_sub_le _ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht] at htri
  have habs := le_abs_self R
  linarith

end MaxLatticeFree.Geometry.Proof
-- End PolyRecession

-- Begin FacetLatticePoint

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma bounded_irredundant_lattice_point (Γ : AddSubgroup E)
    (hΓ : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ, ‖g‖ < ε → g = 0)
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hS : MaxFree Γ (polyBody a b))
    (hint : (interior (polyBody a b)).Nonempty)
    (hbounded : Bornology.IsBounded (polyBody a b))
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j)
    (i : ι) : ∃ z ∈ Γ, a i z = b i ∧ ∀ j, j ≠ i → a j z < b j := by
  classical
  have hne : (polyBody a b).Nonempty := hint.mono interior_subset
  have ha := irredundant_rows_ne_zero a b hne hw
  let K := polyBody a (fun j => b j+1)
  have hK : IsCompact K := polyBody_compact a _ (polyBody_recession_zero a b hne hbounded)
  let Z := K ∩ (Γ : Set E)
  have hZ : Z.Finite := finite_compact_inter_group Γ hΓ hK
  let : Fintype Z := hZ.fintype
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0, δ < 1 ∧
      ∀ z : Z, b i < a i z → δ < a i z-b i := by
    have hz : ∀ z : Z, ∀ᶠ δ : ℝ in 𝓝 0, b i < a i z → δ < a i z-b i := by
      intro z
      by_cases hlt : b i < a i z
      · filter_upwards [gt_mem_nhds (show 0 < a i z-b i by linarith)] with δ hδ
        exact fun _ => hδ
      · exact Eventually.of_forall fun _ h => (hlt h).elim
    filter_upwards [gt_mem_nhds (show (0:ℝ)<1 by norm_num),eventually_all.mpr hz] with δ hδ hz
    exact ⟨hδ,hz⟩
  obtain ⟨δ,hδ,hδ1,hδZ⟩ := hevent.exists_gt
  let c := Function.update b i (b i+δ)
  have hbc : ∀ j, b j ≤ c j := by
    intro j
    by_cases hji : j=i
    · subst j; simp [c,hδ.le]
    · simp [c,hji]
  have hSQ : polyBody a b ⊆ polyBody a c := fun x hx j => (hx j).trans (hbc j)
  by_contra hno
  have hQfree : Free Γ (polyBody a c) := by
    refine ⟨polyBody_convex a c,?_⟩
    intro x hx hxΓ
    have hstrict := interior_polyBody_strict a c ha hx
    have hothers : ∀ j, j ≠ i → a j x < b j := by
      intro j hji
      simpa [c,hji] using hstrict j
    have hle : b i ≤ a i x := by
      by_contra hn
      have hi : a i x < b i := lt_of_not_ge hn
      have hOld : x ∈ interior (polyBody a b) := strict_mem_interior a b (fun j => by
        by_cases hji : j=i
        · simpa [hji] using hi
        · exact hothers j hji)
      exact hS.1.2 x hOld hxΓ
    have hneq : a i x ≠ b i := fun he => hno ⟨x,hxΓ,he,hothers⟩
    have hlt : b i < a i x := lt_of_le_of_ne hle hneq.symm
    have hxK : x ∈ K := by
      intro j
      have hc : c j ≤ b j+1 := by
        by_cases hji : j=i
        · subst j; simp only [c,Function.update_self]; linarith
        · simp [c,hji]
      exact (hstrict j).le.trans hc
    have hgap := hδZ (⟨x,hxK,hxΓ⟩ : Z) hlt
    have hupper : a i x < b i+δ := by simpa [c] using hstrict i
    linarith
  have heq := hS.2 (polyBody a c) hQfree hSQ
  obtain ⟨y,hy,hothers⟩ := exists_strict_face_point a b hint hw i
  have hyQ : y ∈ interior (polyBody a c) := strict_mem_interior a c (fun j => by
    by_cases hji : j=i
    · subst j; simp only [c,Function.update_self,hy]; linarith
    · simpa [c,hji] using hothers j hji)
  rw [heq] at hyQ
  have hcontra := interior_polyBody_strict a b ha hyQ i
  linarith

end MaxLatticeFree.Geometry.Proof
-- End FacetLatticePoint

-- Begin FullPolyhedral

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma full_maxFree_system (Γ : AddSubgroup E) (hspan : Submodule.span ℝ (Γ : Set E)=⊤)
    {S : Set E} (hS : MaxFree Γ S) (hint : (interior S).Nonempty) :
    ∃ (t : ℕ) (a : Fin t → E →ₗ[ℝ] ℝ) (b : Fin t → ℝ), S=polyBody a b ∧
      (∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j) ∧
      (∀ i, ∃ z ∈ Γ, a i z=b i ∧ ∀ j, j ≠ i → a j z < b j) := by
  classical
  obtain ⟨L,hq⟩ := bounded_quotient Γ hspan hS hint
  let Q := Lᗮ
  let P : Set Q := Subtype.val ⁻¹' S
  let Γ' := Γ.map Q.orthogonalProjectionOnto.toLinearMap.toAddMonoidHom
  change IsCompact P ∧ (interior P).Nonempty ∧ MaxFree Γ' P ∧
    S=Q.orthogonalProjectionOnto ⁻¹' P ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ', ‖g‖ < ε → g=0) at hq
  obtain ⟨hc,hi,hm,he,hdis⟩ := hq
  have hp := bounded_maxFree_polyhedral Γ' hdis hm hi hc.isBounded
  obtain ⟨t,a,b,hP,hw⟩ := polyhedral_irredundant hp
  have hm' : MaxFree Γ' (polyBody a b) := hP ▸ hm
  have hi' : (interior (polyBody a b)).Nonempty := hP ▸ hi
  have hb' : Bornology.IsBounded (polyBody a b) := hP ▸ hc.isBounded
  let aa : Fin t → E →ₗ[ℝ] ℝ := fun i => (a i).comp Q.orthogonalProjectionOnto.toLinearMap
  refine ⟨t,aa,b,?_,?_,?_⟩
  · rw [he,hP]
    rfl
  · intro i
    obtain ⟨x,hx,hothers⟩ := hw i
    refine ⟨(x:E),?_,?_⟩
    · simpa [aa,Q.orthogonalProjectionOnto_mem_subspace_eq_self] using hx
    · intro j hji
      simpa [aa,Q.orthogonalProjectionOnto_mem_subspace_eq_self] using hothers j hji
  · intro i
    obtain ⟨z,hz,heq,hothers⟩ := bounded_irredundant_lattice_point Γ' hdis a b hm' hi' hb' hw i
    obtain ⟨x,hx,hxz⟩ := AddSubgroup.mem_map.mp hz
    change Q.orthogonalProjectionOnto x=z at hxz
    refine ⟨x,hx,?_,?_⟩
    · change a i (Q.orthogonalProjectionOnto x)=b i
      rw [hxz]
      exact heq
    · intro j hji
      change a j (Q.orthogonalProjectionOnto x)<b j
      rw [hxz]
      exact hothers j hji

end MaxLatticeFree.Geometry.Proof
-- End FullPolyhedral

-- Begin SectionInterior

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma section_interior (V : Submodule ℝ E) {S : Set E} (hS : Convex ℝ S)
    (hmeet : ∃ p : V, (p:E) ∈ interior S) :
    (Subtype.val : V → E) ⁻¹' interior S = interior ((Subtype.val : V → E) ⁻¹' S) := by
  apply Subset.antisymm (preimage_interior_subset_interior_preimage continuous_subtype_val)
  intro x hx
  obtain ⟨p,hp⟩ := hmeet
  have hc : Continuous (fun t : ℝ => x+t • (x-p)) := by fun_prop
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, x+t • (x-p) ∈ (Subtype.val : V → E) ⁻¹' S := by
    have ht := hc.tendsto 0
    simp only [zero_smul,add_zero] at ht
    exact ht.eventually (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨t,ht,hy⟩ := hevent.exists_gt
  have hden : 0<1+t := by linarith
  have hsum : t/(1+t)+(1/(1+t):ℝ)=1 := by field_simp; ring
  have hh := hS.combo_interior_self_mem_interior hp hy
    (div_pos ht hden) (div_nonneg zero_le_one hden.le) hsum
  have heq : (t/(1+t)) • (p:E)+(1/(1+t):ℝ) • ((x:E)+t • ((x:E)-(p:E)))=(x:E) := by
    calc
      _ = ((1+t)/(1+t)) • (x:E)+(t/(1+t)-t/(1+t)) • (p:E) := by
        simp only [div_eq_mul_inv]
        module
      _ = (x:E) := by simp [hden.ne']
  change (t/(1+t)) • (p:E)+(1/(1+t):ℝ) • ((x:E)+t • ((x:E)-(p:E))) ∈ interior S at hh
  rwa [heq] at hh

end MaxLatticeFree.Geometry.Proof
-- End SectionInterior

-- Begin SectionMaximality

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma section_convexJoin (V : Submodule ℝ E) {S : Set E} {K : Set V}
    (hS : S.Nonempty) (hK : Convex ℝ K)
    (hSK : (Subtype.val : V → E) ⁻¹' S ⊆ K) :
    (Subtype.val : V → E) ⁻¹' convexJoin ℝ S (Subtype.val '' K) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨u,hu,_,⟨v,hv,rfl⟩,r,s,hr,hs,hrs,he⟩ := mem_convexJoin.mp hx
    by_cases hr0 : r=0
    · have hs1 : s=1 := by linarith
      have hvx : v=x := Subtype.ext (by simpa [hr0,hs1] using he)
      exact hvx ▸ hv
    · have huV : u ∈ V := by
        have hh : r • u ∈ V := by
          have heq : r • u=(x:E)-s • (v:E) := by rw [← he]; abel
          rw [heq]
          exact V.sub_mem x.property (V.smul_mem s v.property)
        have hh' := V.smul_mem r⁻¹ hh
        simpa only [smul_smul,inv_mul_cancel₀ hr0,one_smul] using hh'
      let y : V := ⟨u,huV⟩
      have hy : y ∈ K := hSK hu
      have hcomb := hK hy hv hr hs hrs
      have hxeq : r • y+s • v=x := Subtype.ext he
      exact hxeq ▸ hcomb
  · intro hx
    exact subset_convexJoin_right hS (mem_image_of_mem _ hx)

lemma section_maxFree (Γ : AddSubgroup E) (V : Submodule ℝ E)
    (hΓ : (Γ : Set E) ⊆ (V : Set E)) {S : Set E} (hS : MaxFree Γ S)
    (hmeet : ∃ p : V, (p:E) ∈ interior S) :
    MaxFree (Γ.comap V.subtype.toAddMonoidHom) ((Subtype.val : V → E) ⁻¹' S) := by
  have hne : S.Nonempty := by
    obtain ⟨p,hp⟩ := hmeet
    exact ⟨p,interior_subset hp⟩
  have hfree : Free (Γ.comap V.subtype.toAddMonoidHom) ((Subtype.val : V → E) ⁻¹' S) := by
    refine ⟨hS.1.1.linear_preimage V.subtype,?_⟩
    intro x hx hxΓ
    rw [← section_interior V hS.1.1 hmeet] at hx
    exact hS.1.2 x hx hxΓ
  refine ⟨hfree,?_⟩
  intro K hK hSK
  let T := convexJoin ℝ S (Subtype.val '' K)
  have hTK : (Subtype.val : V → E) ⁻¹' T=K := section_convexJoin V hne hK.1 hSK
  have hKne : K.Nonempty := by
    obtain ⟨p,hp⟩ := hmeet
    have hpS : (p:E)∈S := interior_subset hp
    exact ⟨p,hSK hpS⟩
  have hST : S ⊆ T := subset_convexJoin_left (hKne.image _)
  have hTfree : Free Γ T := by
    refine ⟨hS.1.1.convexJoin (hK.1.linear_image V.subtype),?_⟩
    intro x hx hxΓ
    let y : V := ⟨x,hΓ hxΓ⟩
    have hy : y ∈ interior ((Subtype.val : V → E) ⁻¹' T) :=
      preimage_interior_subset_interior_preimage continuous_subtype_val hx
    rw [hTK] at hy
    exact hK.2 y hy hxΓ
  have he := hS.2 T hTfree hST
  rw [← hTK,he]

end MaxLatticeFree.Geometry.Proof
-- End SectionMaximality

-- Begin FaceSupportUnique

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
lemma support_kernel_at_strict_face (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (i : ι) {z : E} (hz : a i z=b i) (hstrict : ∀ j, j ≠ i → a j z<b j)
    (g : E →ₗ[ℝ] ℝ) (hg : ∀ x ∈ polyBody a b, g x≤g z) :
    LinearMap.ker (a i) ≤ LinearMap.ker g := by
  have hzP : z ∈ polyBody a b := by
    intro j
    by_cases hji : j=i
    · simpa [hji] using hz.le
    · exact (hstrict j hji).le
  intro d hd
  have hd0 : a i d=0 := hd
  have hactive : ∀ j, a j z=b j → a j d=0 := by
    intro j hj
    by_cases hji : j=i
    · simpa [hji] using hd0
    · exact ((hstrict j hji).ne hj).elim
  have hh := feasible_kernel_nhds hzP hactive
  obtain ⟨t,ht,hpos⟩ := hh.exists_gt
  obtain ⟨s,hs,hneg⟩ := hh.exists_lt
  have hp := hg _ hpos
  have hn := hg _ hneg
  simp only [map_add,map_smul,smul_eq_mul] at hp hn
  change g d=0
  nlinarith

lemma support_pos_multiple (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (ha : ∀ i, a i≠0) (hint : (interior (polyBody a b)).Nonempty)
    (i : ι) {z : E} (hz : a i z=b i) (hstrict : ∀ j, j ≠ i → a j z<b j)
    (g : E →ₗ[ℝ] ℝ) (hg0 : g≠0) (hg : ∀ x ∈ polyBody a b, g x≤g z) :
    ∃ c : ℝ, 0<c ∧ ∀ x, g x=c*a i x := by
  have hker := support_kernel_at_strict_face a b i hz hstrict g hg
  obtain ⟨q,hq⟩ := LinearMap.surjective (ha i) (1:ℝ)
  have he : ∀ x, g x=g q*a i x := by
    intro x
    have hh : x-a i x • q ∈ LinearMap.ker (a i) := by
      change a i (x-a i x • q)=0
      simp [map_sub,map_smul,hq]
    have hzero : g (x-a i x • q)=0 := hker hh
    simp only [map_sub,map_smul,smul_eq_mul] at hzero
    nlinarith
  have hgn : g q≠0 := by
    intro hq0
    apply hg0
    ext x
    simpa [hq0] using he x
  obtain ⟨p,hp⟩ := hint
  have hpi := interior_polyBody_strict a b ha hp i
  have hgP := hg p (interior_subset hp)
  rw [he p,he z,hz] at hgP
  have hnonneg : 0≤g q := by nlinarith
  exact ⟨g q,lt_of_le_of_ne hnonneg hgn.symm,he⟩

end MaxLatticeFree.Geometry.Proof
-- End FaceSupportUnique

-- Begin SectionSupportSystem

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma section_support_system (Γ : AddSubgroup E) (V : Submodule ℝ E)
    (hΓ : (Γ : Set E) ⊆ (V : Set E))
    (hspan : Submodule.span ℝ (Γ.comap V.subtype.toAddMonoidHom : Set V)=⊤)
    {S : Set E} (hS : MaxFree Γ S) (hmeet : ∃ p : V, (p:E) ∈ interior S) :
    ∃ (t : ℕ) (g : Fin t → E →ₗ[ℝ] ℝ) (d : Fin t → ℝ), S=polyBody g d ∧
      (∀ i, ∃ x : V, d i < g i x ∧ ∀ j, j ≠ i → g j x ≤ d j) ∧
      (∀ i, ∃ z : V, (z:E)∈Γ ∧ g i z=d i ∧ ∀ j, j ≠ i → g j z<d j) := by
  classical
  let ΓV := Γ.comap V.subtype.toAddMonoidHom
  let P : Set V := Subtype.val ⁻¹' S
  have hP : MaxFree ΓV P := section_maxFree Γ V hΓ hS hmeet
  have hiP : (interior P).Nonempty := by
    obtain ⟨p,hp⟩ := hmeet
    exact ⟨p,preimage_interior_subset_interior_preimage continuous_subtype_val hp⟩
  obtain ⟨t,a,b,heP,hw,hz⟩ := full_maxFree_system ΓV hspan hP hiP
  choose z hzΓ hzi hzothers using hz
  have hsupp : ∀ i, ∃ f : E →L[ℝ] ℝ, f≠0 ∧ ∀ x∈S, f x≤f (z i) := by
    intro i
    apply supporting_functional hS.1.1
      (by obtain ⟨p,hp⟩ := hmeet; exact ⟨p,hp⟩)
    intro hint
    exact hS.1.2 (z i) hint (hzΓ i)
  choose f hf hfbound using hsupp
  let g : Fin t → E →ₗ[ℝ] ℝ := fun i => (f i).toLinearMap
  let d : Fin t → ℝ := fun i => g i (z i)
  have hgi : ∀ i, (g i).comp V.subtype ≠ 0 := by
    intro i he
    obtain ⟨p,hp⟩ := hmeet
    have hsub : S ⊆ polyBody (fun _ : Unit => g i) (fun _ => d i) := fun x hx _ => hfbound i x hx
    have hgn : g i≠0 := by
      intro hh; apply hf i; ext x; exact congrArg (fun l : E →ₗ[ℝ] ℝ => l x) hh
    have hh := interior_polyBody_strict (fun _ : Unit => g i) (fun _ => d i)
      (fun _ => hgn) (interior_mono hsub hp) ()
    have hp0 := congrArg (fun l : V →ₗ[ℝ] ℝ => l p) he
    have hz0 := congrArg (fun l : V →ₗ[ℝ] ℝ => l (z i)) he
    change g i p=0 at hp0
    change g i (z i)=0 at hz0
    change g i p<g i (z i) at hh
    linarith
  have hiA : (interior (polyBody a b)).Nonempty := heP ▸ hiP
  have ha := irredundant_rows_ne_zero a b (hiA.mono interior_subset) hw
  have hscale : ∀ i, ∃ c : ℝ, 0<c ∧ ∀ x : V, g i x=c*a i x := by
    intro i
    apply support_pos_multiple a b ha hiA i (hzi i) (hzothers i)
      ((g i).comp V.subtype) (hgi i)
    intro x hx
    apply hfbound i x
    change x∈P
    rwa [heP]
  choose c hc hceq using hscale
  have hd : ∀ i, d i=c i*b i := by
    intro i
    dsimp only [d]
    rw [hceq,hzi]
  have hSQ : S ⊆ polyBody g d := fun x hx i => hfbound i x hx
  have hQfree : Free Γ (polyBody g d) := by
    refine ⟨polyBody_convex g d,?_⟩
    intro x hx hxΓ
    let y : V := ⟨x,hΓ hxΓ⟩
    have hstrict : ∀ i, g i x<d i := interior_polyBody_strict g d (fun i hh => by
      apply hf i; ext q; exact congrArg (fun l : E →ₗ[ℝ] ℝ => l q) hh) hx
    have hy : y∈interior (polyBody a b) := strict_mem_interior a b (fun i => by
      have hh : g i y<d i := hstrict i
      rw [hceq,hd] at hh
      nlinarith [hc i])
    rw [← heP] at hy
    exact hP.1.2 y hy hxΓ
  have heS := hS.2 (polyBody g d) hQfree hSQ
  refine ⟨t,g,d,heS.symm,?_,?_⟩
  · intro i
    obtain ⟨x,hx,hothers⟩ := hw i
    refine ⟨x,?_,?_⟩
    · rw [hceq,hd]
      exact mul_lt_mul_of_pos_left hx (hc i)
    · intro j hji
      rw [hceq,hd]
      exact mul_le_mul_of_nonneg_left (hothers j hji) (hc j).le
  · intro i
    refine ⟨z i,hzΓ i,rfl,?_⟩
    intro j hji
    rw [hceq,hd]
    exact mul_lt_mul_of_pos_left (hzothers i j hji) (hc j)

end MaxLatticeFree.Geometry.Proof
-- End SectionSupportSystem

-- Begin FacetRestriction

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def FacetsRestrict (V : Submodule ℝ E) (S : Set E) : Prop :=
  (∀ F, GFacet S F → GFacet ((Subtype.val : V → E) ⁻¹' S) (Subtype.val ⁻¹' F)) ∧
  (∀ F G, GFacet S F → GFacet S G →
    (Subtype.val : V → E) ⁻¹' F=Subtype.val ⁻¹' G → F=G) ∧
  (∀ G, GFacet ((Subtype.val : V → E) ⁻¹' S) G →
    ∃ F, GFacet S F ∧ (Subtype.val : V → E) ⁻¹' F=G)

lemma rowFace_injective {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hint : (interior (polyBody a b)).Nonempty)
    (hw : ∀ i, ∃ x : E, b i < a i x ∧ ∀ j, j ≠ i → a j x ≤ b j) :
    Function.Injective (rowFace a b) := by
  intro i j he
  obtain ⟨z,hz,hothers⟩ := exists_strict_face_point a b hint hw i
  have hzP : z∈polyBody a b := by
    intro k
    by_cases hki : k=i
    · simpa [hki] using hz.le
    · exact (hothers k hki).le
  have hzj : z∈rowFace a b j := he ▸ (show z∈rowFace a b i from ⟨hzP,hz⟩)
  by_contra hij
  exact (hothers j (Ne.symm hij)).ne hzj.2

lemma system_facets_restrict (V : Submodule ℝ E) {t : ℕ}
    (g : Fin t → E →ₗ[ℝ] ℝ) (d : Fin t → ℝ)
    (hi : (interior (polyBody g d)).Nonempty)
    (hiV : (interior ((Subtype.val : V → E) ⁻¹' polyBody g d)).Nonempty)
    (hw : ∀ i, ∃ x : V, d i < g i x ∧ ∀ j, j ≠ i → g j x ≤ d j) :
    FacetsRestrict V (polyBody g d) := by
  let a : Fin t → V →ₗ[ℝ] ℝ := fun i => (g i).comp V.subtype
  have heP : (Subtype.val : V → E) ⁻¹' polyBody g d=polyBody a d := rfl
  have hwE : ∀ i, ∃ x : E, d i < g i x ∧ ∀ j, j ≠ i → g j x ≤ d j := by
    intro i; obtain ⟨x,hx,hh⟩ := hw i; exact ⟨x,hx,hh⟩
  have hwV : ∀ i, ∃ x : V, d i < a i x ∧ ∀ j, j ≠ i → a j x ≤ d j := hw
  have hiA : (interior (polyBody a d)).Nonempty := hiV
  have hface : ∀ i, (Subtype.val : V → E) ⁻¹' rowFace g d i=rowFace a d i := fun _ => rfl
  refine ⟨?_,?_,?_⟩
  · intro F hF
    obtain ⟨i,rfl⟩ := gFacet_eq_rowFace g d hi hwE hF
    rw [heP,hface]
    exact rowFace_is_gFacet a d hiA hwV i
  · intro F G hF hG he
    obtain ⟨i,rfl⟩ := gFacet_eq_rowFace g d hi hwE hF
    obtain ⟨j,rfl⟩ := gFacet_eq_rowFace g d hi hwE hG
    have hij : i=j := rowFace_injective a d hiA hwV (by simpa only [hface] using he)
    rw [hij]
  · intro G hG
    rw [heP] at hG
    obtain ⟨i,rfl⟩ := gFacet_eq_rowFace a d hiA hwV hG
    exact ⟨rowFace g d i,rowFace_is_gFacet g d hi hwE i,hface i⟩

lemma full_section_classification_forward (Γ : AddSubgroup E) (V : Submodule ℝ E)
    (hΓ : (Γ : Set E) ⊆ (V : Set E))
    (hspan : Submodule.span ℝ (Γ.comap V.subtype.toAddMonoidHom : Set V)=⊤)
    {S : Set E} (hS : MaxFree Γ S) (hmeet : ∃ p : V, (p:E)∈interior S) :
    Polyhedral S ∧ MaxFree (Γ.comap V.subtype.toAddMonoidHom)
      ((Subtype.val : V → E) ⁻¹' S) ∧ FacetsRestrict V S := by
  obtain ⟨t,g,d,he,hw,_⟩ := section_support_system Γ V hΓ hspan hS hmeet
  refine ⟨⟨t,g,d,he⟩,section_maxFree Γ V hΓ hS hmeet,?_⟩
  have hi : (interior S).Nonempty := by obtain ⟨p,hp⟩ := hmeet; exact ⟨p,hp⟩
  have hiV : (interior ((Subtype.val : V → E) ⁻¹' S)).Nonempty := by
    obtain ⟨p,hp⟩ := hmeet
    exact ⟨p,preimage_interior_subset_interior_preimage continuous_subtype_val hp⟩
  rw [he] at hi hiV ⊢
  exact system_facets_restrict V g d hi hiV hw

end MaxLatticeFree.Geometry.Proof
-- End FacetRestriction

-- Begin NativeFacetRestriction

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {n : ℕ}

lemma nested_image_restriction (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (A : Set W) :
    (Subtype.val : W → _) '' ((Subtype.val : V.comap W.subtype → W) ''
      ((Subtype.val : V.comap W.subtype → W) ⁻¹' A)) =
      ((Subtype.val : W → _) '' A) ∩ (V:Set _) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨⟨y,hy,rfl⟩,y.property⟩
  · rintro ⟨⟨y,hy,rfl⟩,hyV⟩
    exact ⟨y,⟨⟨y,hyV⟩,hy,rfl⟩,rfl⟩

lemma nativeFacetsRestrict_iff (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hVW : V ≤ W) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ (W:Set _)) :
    ((∀ F, IsFacet S F → IsFacet (S ∩ (V:Set _)) (F ∩ (V:Set _))) ∧
      (∀ F G, IsFacet S F → IsFacet S G → F ∩ (V:Set _) = G ∩ (V:Set _) → F=G) ∧
      (∀ G, IsFacet (S ∩ (V:Set _)) G → ∃ F, IsFacet S F ∧ F ∩ (V:Set _) = G)) ↔
      FacetsRestrict (V.comap W.subtype) ((Subtype.val : W → _) ⁻¹' S) := by
  let P : Set W := (Subtype.val : W → _) ⁻¹' S
  let U := V.comap W.subtype
  let e : W → EuclideanSpace ℝ (Fin n) := Subtype.val
  let v : U → W := Subtype.val
  have hPS : e '' P = S := subtype_image_preimage_of_subset W S hS
  have hsection : e '' (v '' (v ⁻¹' P)) = S ∩ (V:Set _) := by
    rw [nested_image_restriction,hPS]
  have hfacet (A : Set W) : IsFacet S (e '' A) ↔ GFacet P A := by
    rw [nativeFacet_iff_gFacet,←hPS,gFacet_subtype_image_iff]
  have hfacetV (A : Set U) : IsFacet (S ∩ (V:Set _)) (e '' (v '' A)) ↔ GFacet (v ⁻¹' P) A := by
    rw [nativeFacet_iff_gFacet,←hsection,gFacet_subtype_image_iff,gFacet_subtype_image_iff]
  have hpre (A : Set W) : e '' (v '' (v ⁻¹' A)) = (e '' A) ∩ (V:Set _) := nested_image_restriction V W A
  constructor
  · rintro ⟨hn,hi,hs⟩
    refine ⟨?_,?_,?_⟩
    · intro A hA
      apply (hfacetV _).mp
      rw [hpre]
      exact hn _ ((hfacet A).mpr hA)
    · intro A B hA hB he
      have hh : e '' A = e '' B := hi _ _ ((hfacet A).mpr hA) ((hfacet B).mpr hB) (by
        rw [←hpre A,←hpre B,he])
      exact Set.image_injective.mpr Subtype.val_injective hh
    · intro G hG
      obtain ⟨F,hF,he⟩ := hs _ ((hfacetV G).mpr hG)
      have hFW : F ⊆ (W:Set _) := ((nativeFacet_iff_gFacet S F).mp hF).subset.trans hS
      let A : Set W := e ⁻¹' F
      have hAF : e '' A = F := subtype_image_preimage_of_subset W F hFW
      refine ⟨A,(hfacet A).mp (hAF.symm ▸ hF),?_⟩
      apply Set.image_injective.mpr Subtype.val_injective
      apply Set.image_injective.mpr Subtype.val_injective
      rw [hpre,hAF,he]
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro F hF
      have hFW : F ⊆ (W:Set _) := ((nativeFacet_iff_gFacet S F).mp hF).subset.trans hS
      have hAF := subtype_image_preimage_of_subset W F hFW
      have hg : GFacet P (e ⁻¹' F) := (hfacet _).mp (hAF.symm ▸ hF)
      have hh := (hfacetV _).mpr (h.1 _ hg)
      rwa [hpre,hAF] at hh
    · intro F G hF hG he
      have hFW : F ⊆ (W:Set _) := ((nativeFacet_iff_gFacet S F).mp hF).subset.trans hS
      have hGW : G ⊆ (W:Set _) := ((nativeFacet_iff_gFacet S G).mp hG).subset.trans hS
      have hAF := subtype_image_preimage_of_subset W F hFW
      have hAG := subtype_image_preimage_of_subset W G hGW
      have hgF : GFacet P (e ⁻¹' F) := (hfacet _).mp (hAF.symm ▸ hF)
      have hgG : GFacet P (e ⁻¹' G) := (hfacet _).mp (hAG.symm ▸ hG)
      have hpreEq : v ⁻¹' (e ⁻¹' F) = v ⁻¹' (e ⁻¹' G) := by
        apply Set.image_injective.mpr Subtype.val_injective
        apply Set.image_injective.mpr Subtype.val_injective
        rw [hpre,hpre,hAF,hAG,he]
      have hh := h.2.1 _ _ hgF hgG hpreEq
      rw [←hAF,←hAG,hh]
    · intro G hG
      have hGV : G ⊆ (V:Set _) := ((nativeFacet_iff_gFacet _ G).mp hG).subset.trans inter_subset_right
      let B : Set U := v ⁻¹' (e ⁻¹' G)
      have hBG : e '' (v '' B) = G := nested_subtype_image_preimage V W hVW G hGV
      have hg : GFacet (v ⁻¹' P) B := (hfacetV B).mp (hBG.symm ▸ hG)
      obtain ⟨A,hA,he⟩ := h.2.2 _ hg
      refine ⟨e '' A,(hfacet A).mpr hA,?_⟩
      rw [←hpre,he,hBG]

end MaxLatticeFree.Geometry.Proof
-- End NativeFacetRestriction

-- Begin FacetMaximality

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma strict_face_enters_interior (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {i : ι} {z x : E} (hz : a i z=b i)
    (hothers : ∀ j, j ≠ i → a j z < b j) (hx : b i < a i x)
    {K : Set E} (hK : Convex ℝ K) (hSK : polyBody a b ⊆ K) (hxK : x∈K) :
    z ∈ interior K := by
  have hh : ∀ j, ∀ᶠ t : ℝ in 𝓝 0, 0<t → a j (z+t • (z-x))<b j := by
    intro j
    by_cases hji : j=i
    · subst j
      exact Eventually.of_forall fun t ht => by
        simp only [map_add,map_smul,smul_eq_mul,map_sub,hz]
        have hprod := mul_neg_of_pos_of_neg ht (show b i-a i x<0 by linarith)
        linarith
    · have hc : Tendsto (fun t : ℝ => a j z+t*(a j z-a j x)) (𝓝 0) (𝓝 (a j z)) := by
        have hc : Continuous (fun t : ℝ => a j z+t*(a j z-a j x)) := by fun_prop
        simpa using hc.tendsto 0
      filter_upwards [hc.eventually (gt_mem_nhds (hothers j hji))] with t ht
      intro _
      simpa only [map_add,map_smul,smul_eq_mul,map_sub] using ht
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, 0<t → z+t • (z-x) ∈ interior (polyBody a b) := by
    filter_upwards [eventually_all.mpr hh] with t ht hp
    exact strict_mem_interior a b (fun j => ht j hp)
  obtain ⟨t,ht,hp⟩ := hevent.exists_gt
  have hint : z+t • (z-x) ∈ interior K := interior_mono hSK (hp ht)
  have hden : 0 < 1+t := by linarith
  have hsum : (1/(1+t):ℝ)+t/(1+t)=1 := by field_simp
  have hmem := hK.combo_interior_self_mem_interior hint hxK
    (div_pos zero_lt_one hden) (div_nonneg ht.le hden.le) hsum
  have heq : (1/(1+t):ℝ) • (z+t • (z-x))+(t/(1+t)) • x=z := by
    calc
      _ = ((1+t)/(1+t)) • z+(t/(1+t)-t/(1+t)) • x := by
        simp only [div_eq_mul_inv]
        module
      _ = z := by simp [hden.ne']
  rwa [heq] at hmem

lemma system_lattice_points_maxFree (Γ : AddSubgroup E)
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (hfree : Free Γ (polyBody a b))
    (hz : ∀ i, ∃ z ∈ Γ, a i z=b i ∧ ∀ j, j ≠ i → a j z < b j) :
    MaxFree Γ (polyBody a b) := by
  classical
  refine ⟨hfree,?_⟩
  intro K hK hSK
  apply Subset.antisymm ?_ hSK
  intro x hx
  by_contra hn
  change ¬ ∀ i, a i x≤b i at hn
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  obtain ⟨z,hzΓ,hzi,hzothers⟩ := hz i
  exact hK.2 z (strict_face_enters_interior a b hzi hzothers hi hK.1 hSK hx) hzΓ

end MaxLatticeFree.Geometry.Proof
-- End FacetMaximality

-- Begin LowerDimensional

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma convex_empty_interior_hyperplane {S : Set E} (hS : Convex ℝ S)
    (hne : S.Nonempty) (hi : interior S = ∅) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∃ b : ℝ, S ⊆ {x | f x = b} := by
  let A := affineSpan ℝ S
  have hA : A ≠ ⊤ := by
    intro h
    have hh := hS.interior_nonempty_iff_affineSpan_eq_top.mpr h
    simp [hi] at hh
  have hd : A.direction ≠ ⊤ := by
    intro h
    exact hA ((AffineSubspace.direction_eq_top_iff_of_nonempty
      (hne.mono (subset_affineSpan ℝ S))).mp h)
  have hp : A.directionᗮ ≠ ⊥ := by
    intro h
    exact hd (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨x,hx⟩ := hne
  let f : E →L[ℝ] ℝ := innerSL ℝ v
  have hf : f ≠ 0 := by
    intro h
    have hh := congrArg (fun g : E →L[ℝ] ℝ => g v) h
    have : inner ℝ v v = 0 := by simpa [f] using hh
    exact hv0 (inner_self_eq_zero.mp this)
  refine ⟨f,hf,f x,?_⟩
  intro y hy
  have hm : y-x ∈ A.direction := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ S hy) (subset_affineSpan ℝ S hx)
  have hh := A.direction.inner_right_of_mem_orthogonal hm hv
  change inner ℝ (y-x) v = 0 at hh
  change inner ℝ v y = inner ℝ v x
  rw [inner_sub_left] at hh
  rw [←real_inner_comm v y,←real_inner_comm v x]
  linarith

lemma maxFree_empty_interior_hyperplane [Nontrivial E] (Γ : AddSubgroup E)
    {S : Set E} (hS : MaxFree Γ S) (hi : interior S = ∅) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∃ b : ℝ, S = {x | f x = b} := by
  have hne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hn
    obtain ⟨v,hv⟩ := exists_ne (0:E)
    let f : E →L[ℝ] ℝ := innerSL ℝ v
    have hf : f ≠ 0 := by
      intro h
      have hh := congrArg (fun g : E →L[ℝ] ℝ => g v) h
      exact hv (by simpa [f] using hh)
    have hfree : Free Γ {x : E | f x = 0} :=
      ⟨(convex_singleton 0).linear_preimage f.toLinearMap,by simp [hyperplane_interior f hf 0]⟩
    have hh := hS.2 _ hfree (by simp [he])
    have hz : (0:E) ∈ {x : E | f x = 0} := by simp
    rw [hh,he] at hz
    exact hz
  obtain ⟨f,hf,b,hsub⟩ := convex_empty_interior_hyperplane hS.1.1 hne hi
  refine ⟨f,hf,b,(hS.2 _ ?_ hsub).symm⟩
  exact ⟨(convex_singleton b).linear_preimage f.toLinearMap,by simp [hyperplane_interior f hf b]⟩

end MaxLatticeFree.Geometry.Proof
-- End LowerDimensional

-- Begin NoLowerFacet

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma no_gFacet_level (f : E →ₗ[ℝ] ℝ) (b : ℝ) (F : Set E) :
    ¬ GFacet {x | f x=b} F := by
  intro hF
  obtain ⟨g,c,hbound,he⟩ := hF.2.2
  obtain ⟨z,hz⟩ := hF.1
  have hzS : f z=b := hF.subset hz
  have hzc : g z=c := (show z∈{x | f x=b} ∩ {x | g x=c} from he ▸ hz).2
  have hFS : F={x | f x=b} := by
    apply Subset.antisymm hF.subset
    intro x hx
    have hy : (2:ℝ) • z-x ∈ {x | f x=b} := by
      change f ((2:ℝ) • z-x)=b
      simp only [map_sub,map_smul,smul_eq_mul,hzS]
      change 2*b-f x=b
      change f x=b at hx
      linarith
    have h1 := hbound x hx
    have h2 := hbound _ hy
    simp only [map_sub,map_smul,smul_eq_mul,hzc] at h2
    rw [he]
    exact ⟨hx,by change g x=c; linarith⟩
  have hd := hF.2.1
  rw [hFS] at hd
  omega

lemma maxFree_empty_interior_no_gFacet [FiniteDimensional ℝ E]
    (Γ : AddSubgroup E) {S : Set E} (hS : MaxFree Γ S) (hi : interior S=∅)
    (F : Set E) : ¬ GFacet S F := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have he : S=∅ := by
      have hop : IsOpen S := isOpen_discrete S
      rwa [hop.interior_eq] at hi
    intro hF
    obtain ⟨x,hx⟩ := hF.1
    have hh := hF.subset hx
    simp [he] at hh
  · obtain ⟨f,_,b,he⟩ := maxFree_empty_interior_hyperplane Γ hS hi
    rw [he]
    exact no_gFacet_level f.toLinearMap b F

end MaxLatticeFree.Geometry.Proof
-- End NoLowerFacet

-- Begin SectionConverse

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma full_section_classification_reverse (Γ : AddSubgroup E) (V : Submodule ℝ E)
    (hΓ : (Γ : Set E) ⊆ (V : Set E))
    (hspan : Submodule.span ℝ (Γ.comap V.subtype.toAddMonoidHom : Set V)=⊤)
    {S : Set E} (hpoly : Polyhedral S) (hiS : (interior S).Nonempty)
    (hP : MaxFree (Γ.comap V.subtype.toAddMonoidHom) ((Subtype.val : V → E) ⁻¹' S))
    (hfacets : FacetsRestrict V S) : MaxFree Γ S := by
  classical
  obtain ⟨t,g,d,heS,hw⟩ := polyhedral_irredundant hpoly
  subst S
  let P : Set V := Subtype.val ⁻¹' polyBody g d
  let ΓV := Γ.comap V.subtype.toAddMonoidHom
  have hfree : Free Γ (polyBody g d) := by
    refine ⟨polyBody_convex g d,?_⟩
    intro x hx hxΓ
    let y : V := ⟨x,hΓ hxΓ⟩
    have hy : y∈interior P := preimage_interior_subset_interior_preimage continuous_subtype_val hx
    exact hP.1.2 y hy hxΓ
  have hiP : (interior P).Nonempty := by
    by_contra hn
    have hempty : interior P=∅ := not_nonempty_iff_eq_empty.mp hn
    have hfalse : ∀ i : Fin t, False := by
      intro i
      have hF := hfacets.1 (rowFace g d i) (rowFace_is_gFacet g d hiS hw i)
      exact maxFree_empty_interior_no_gFacet ΓV hP hempty _ hF
    have hz : (0:E)∈interior (polyBody g d) := strict_mem_interior g d (fun i => (hfalse i).elim)
    exact hfree.2 0 hz Γ.zero_mem
  obtain ⟨s,a,b,heP,hwP,hzP⟩ := full_maxFree_system ΓV hspan hP hiP
  change P=polyBody a b at heP
  have hiA : (interior (polyBody a b)).Nonempty := heP ▸ hiP
  apply system_lattice_points_maxFree Γ g d hfree
  intro i
  have hFi := rowFace_is_gFacet g d hiS hw i
  have hGi := hfacets.1 (rowFace g d i) hFi
  change GFacet P ((Subtype.val : V → E) ⁻¹' rowFace g d i) at hGi
  rw [heP] at hGi
  obtain ⟨k,hGi⟩ := gFacet_eq_rowFace a b hiA hwP hGi
  obtain ⟨z,hzΓ,hzk,hzothers⟩ := hzP k
  have hzA : z∈polyBody a b := by
    intro l
    by_cases hl : l=k
    · simpa [hl] using hzk.le
    · exact (hzothers l hl).le
  have hzG : z∈(Subtype.val : V → E) ⁻¹' rowFace g d i := by
    rw [hGi]
    exact ⟨hzA,hzk⟩
  refine ⟨(z:E),hzΓ,hzG.2,?_⟩
  intro j hji
  have hzS : (z:E)∈polyBody g d := hzG.1
  apply lt_of_le_of_ne (hzS j)
  intro hjeq
  have hFj := rowFace_is_gFacet g d hiS hw j
  have hGj := hfacets.1 (rowFace g d j) hFj
  change GFacet P ((Subtype.val : V → E) ⁻¹' rowFace g d j) at hGj
  rw [heP] at hGj
  obtain ⟨l,hGj⟩ := gFacet_eq_rowFace a b hiA hwP hGj
  have hzGj : z∈(Subtype.val : V → E) ⁻¹' rowFace g d j := ⟨hzS,hjeq⟩
  rw [hGj] at hzGj
  have hlk : l=k := by
    by_contra hh
    exact (hzothers l hh).ne hzGj.2
  have hFG : rowFace g d j=rowFace g d i := hfacets.2.1 _ _ hFj hFi (by rw [hGj,hGi,hlk])
  exact hji (rowFace_injective g d hiS hw hFG)

end MaxLatticeFree.Geometry.Proof
-- End SectionConverse

-- Begin NativePolyCase

open Set

namespace MaxLatticeFree.Geometry.Proof

variable {n : ℕ}

lemma native_polyhedral_forward (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V≤W)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ W S)
    (hmeet : ∃ x, x∈intW (W : Set _) S ∧ x∈V) :
    IsPolyhedronIn W S ∧ affDim S=(Module.finrank ℝ W : ℤ) ∧
      IsMaxLambdaFree Λ V (S ∩ (V : Set _)) ∧
      (∀ F, IsFacet S F → IsFacet (S ∩ (V : Set _)) (F ∩ (V : Set _))) ∧
      (∀ F G, IsFacet S F → IsFacet S G → F ∩ (V : Set _)=G ∩ (V : Set _) → F=G) ∧
      (∀ G, IsFacet (S ∩ (V : Set _)) G → ∃ F, IsFacet S F ∧ F ∩ (V : Set _)=G) := by
  let Γ := Λ.comap W.subtype.toAddMonoidHom
  let U : Submodule ℝ W := V.comap W.subtype
  let P : Set W := Subtype.val ⁻¹' S
  have hp : MaxFree Γ P := (nativeMaxFree_iff Λ W S hS.1.1).mp hS
  have hΓ : (Γ : Set W) ⊆ (U : Set W) := fun x hx => native_lattice_subset hΛ hx
  have hspan : Submodule.span ℝ (Γ.comap U.subtype.toAddMonoidHom : Set U)=⊤ :=
    native_nested_span Λ V W hΛ hVW
  have hm : ∃ p : U, (p:W)∈interior P := by
    obtain ⟨x,hx,hxV⟩ := hmeet
    let y : W := ⟨x,hS.1.1 hx.1⟩
    exact ⟨⟨y,hxV⟩,(intW_subtype_iff (W : Set _) S y).mp hx⟩
  obtain ⟨hpoly,hmax,hfac⟩ := full_section_classification_forward Γ U hΓ hspan hp hm
  have hiP : (interior P).Nonempty := by obtain ⟨p,hp⟩ := hm; exact ⟨p,hp⟩
  have hf := (nativeFacetsRestrict_iff V W hVW S hS.1.1).mpr hfac
  exact ⟨(nativePolyhedron_iff W S hS.1.1).mpr hpoly,
    (nativeFullDim_iff W S hS.1.1 hS.1.2.1).mpr hiP,
    (native_section_maxFree_iff Λ V W hVW S).mpr hmax,hf.1,hf.2.1,hf.2.2⟩

lemma native_polyhedral_reverse (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V≤W)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hpoly : IsPolyhedronIn W S) (hd : affDim S=(Module.finrank ℝ W : ℤ))
    (hmax : IsMaxLambdaFree Λ V (S ∩ (V : Set _)))
    (hn : ∀ F, IsFacet S F → IsFacet (S ∩ (V : Set _)) (F ∩ (V : Set _)))
    (hinj : ∀ F G, IsFacet S F → IsFacet S G → F ∩ (V : Set _)=G ∩ (V : Set _) → F=G)
    (hsurj : ∀ G, IsFacet (S ∩ (V : Set _)) G → ∃ F, IsFacet S F ∧ F ∩ (V : Set _)=G) :
    IsMaxLambdaFree Λ W S := by
  have hSW : S⊆(W : Set _) := by obtain ⟨t,a,b,rfl⟩ := hpoly; exact inter_subset_left
  have hconv : Convex ℝ S := by
    obtain ⟨t,a,b,rfl⟩ := hpoly
    exact W.convex.inter (polyBody_convex (fun i => (innerSL ℝ (a i)).toLinearMap) b)
  let Γ := Λ.comap W.subtype.toAddMonoidHom
  let U : Submodule ℝ W := V.comap W.subtype
  let P : Set W := Subtype.val ⁻¹' S
  have hΓ : (Γ : Set W) ⊆ (U : Set W) := fun x hx => native_lattice_subset hΛ hx
  have hspan : Submodule.span ℝ (Γ.comap U.subtype.toAddMonoidHom : Set U)=⊤ :=
    native_nested_span Λ V W hΛ hVW
  have hp : Polyhedral P := (nativePolyhedron_iff W S hSW).mp hpoly
  have hi : (interior P).Nonempty := (nativeFullDim_iff W S hSW hconv).mp hd
  have hm : @MaxFree U U.normedAddCommGroup (Submodule.innerProductSpace U) (Γ.comap U.subtype.toAddMonoidHom) ((Subtype.val : U → W) ⁻¹' P) :=
    (native_section_maxFree_iff Λ V W hVW S).mp hmax
  have hf : FacetsRestrict U P := (nativeFacetsRestrict_iff V W hVW S hSW).mp ⟨hn,hinj,hsurj⟩
  exact (nativeMaxFree_iff Λ W S hSW).mpr
    (full_section_classification_reverse Γ U hΓ hspan hp hi hm hf)

end MaxLatticeFree.Geometry.Proof
-- End NativePolyCase

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

-- Begin SubspaceRestriction

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def restrictFunctional {V W : Submodule ℝ E} (hVW : V ≤ W)
    (f : W →L[ℝ] ℝ) : V →L[ℝ] ℝ := f.comp (V.inclusion hVW).toContinuousLinearMap

lemma restriction_kernel_map {V W : Submodule ℝ E} (hVW : V ≤ W) (f : W →L[ℝ] ℝ) :
    (LinearMap.ker (restrictFunctional hVW f).toLinearMap).map V.subtype =
      (LinearMap.ker f.toLinearMap).map W.subtype ⊓ V := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨⟨y,hVW y.property⟩,hy,rfl⟩,y.property⟩
  · rintro ⟨⟨y,hy,he⟩,hxV⟩
    subst x
    exact ⟨⟨y,hxV⟩,hy,rfl⟩

lemma restriction_group_image (Γ : AddSubgroup E) {V W : Submodule ℝ E}
    (hVW : V ≤ W) (hΓ : (Γ:Set E) ⊆ (V:Set E)) (f : W →L[ℝ] ℝ) :
    f '' (Γ.comap W.subtype.toAddMonoidHom : Set W) =
      restrictFunctional hVW f '' (Γ.comap V.subtype.toAddMonoidHom : Set V) := by
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hΓ hx⟩,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hVW x.property⟩,hx,rfl⟩

omit [FiniteDimensional ℝ E] in
lemma dense_functional_ne_zero (Γ : AddSubgroup E) (f : E →L[ℝ] ℝ)
    (hd : Dense (f '' (Γ:Set E))) : f ≠ 0 := by
  intro hf
  obtain ⟨r,⟨x,hx,he⟩,hr⟩ := hd.exists_mem_open (U := Ioo 1 2) isOpen_Ioo
    (nonempty_Ioo.mpr (by norm_num))
  simp [hf] at he
  subst r
  norm_num at hr

omit [FiniteDimensional ℝ E] in
lemma map_subtype_finrank (W : Submodule ℝ E) (L : Submodule ℝ W) :
    Module.finrank ℝ (L.map W.subtype) = Module.finrank ℝ L := by
  exact (Submodule.equivMapOfInjective W.subtype W.injective_subtype L).finrank_eq.symm

end MaxLatticeFree.Geometry.Proof
-- End SubspaceRestriction

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

-- Begin NativeHyperplaneForward

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {n : ℕ}

lemma native_empty_interior_hyperplane (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (hVW : V ≤ W) (hW : 0 < Module.finrank ℝ W) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsMaxLambdaFree Λ W S) (hi : intW (W:Set _) S = ∅) :
    ∃ v ∈ W, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W ∧
      Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧
      S = v +ᵥ (L:Set _) ∧ Module.finrank ℝ (L ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ V ∧
      ¬ IsLambdaSubspace Λ V (L ⊓ V) := by
  let := Module.nontrivial_of_finrank_pos hW
  let P : Set W := (Subtype.val : W → _) ⁻¹' S
  have hp : MaxFree (Λ.comap W.subtype.toAddMonoidHom) P :=
    (nativeMaxFree_iff Λ W S hS.1.1).mp hS
  have hpi : interior P = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := (intW_subtype_iff (W:Set _) S x).mpr hx
    rw [hi] at hh
    exact hh
  obtain ⟨f,hf,b,he⟩ := maxFree_empty_interior_hyperplane _ hp hpi
  have hd : Dense (f '' (Λ.comap W.subtype.toAddMonoidHom:Set W)) :=
    (maxFree_hyperplane_iff_dense _ f hf b).mp (he ▸ hp)
  have hdV : Dense (restrictFunctional hVW f '' (Λ.comap V.subtype.toAddMonoidHom:Set V)) := by
    rwa [restriction_group_image Λ hVW (native_lattice_subset hΛ) f] at hd
  have hfV := dense_functional_ne_zero _ _ hdV
  let L := (LinearMap.ker f.toLinearMap).map W.subtype
  have hmap : (LinearMap.ker (restrictFunctional hVW f).toLinearMap).map V.subtype = L ⊓ V :=
    restriction_kernel_map hVW f
  obtain ⟨e,he1⟩ := functional_unit f hf
  let v : W := b • e
  have hv : f v = b := by simp [v,he1]
  refine ⟨v,v.property,L,?_,?_,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩; exact y.property
  · rw [map_subtype_finrank]
    exact functional_kernel_codim f hf
  · have himage : (Subtype.val : W → _) '' P = S := by
      exact image_preimage_eq_of_subset (by simpa using hS.1.1)
    rw [←himage,he,←hv]
    exact image_level_eq_vadd_kernel W f v
  · rw [←hmap,map_subtype_finrank]
    exact functional_kernel_codim _ hfV
  · rw [←hmap]
    exact (native_dense_iff_kernel_not_lambda hΛ _ hfV).mp hdV

end MaxLatticeFree.Geometry.Proof
-- End NativeHyperplaneForward

-- Begin NativeHyperplaneReverse

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.Proof
variable {n : ℕ}

lemma native_hyperplane_maximal (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (hVW : V ≤ W) (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ W)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLW : L ≤ W)
    (hLWdim : Module.finrank ℝ L + 1 = Module.finrank ℝ W)
    (hLVdim : Module.finrank ℝ (L ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ V)
    (hirr : ¬ IsLambdaSubspace Λ V (L ⊓ V)) :
    IsMaxLambdaFree Λ W (v +ᵥ (L:Set _)) := by
  let K := L.comap W.subtype
  have hKmap : K.map W.subtype = L := map_subtype_comap_eq W L hLW
  have hKdim : Module.finrank ℝ K + 1 = Module.finrank ℝ W := by
    rw [←hKmap,map_subtype_finrank] at hLWdim
    exact hLWdim
  obtain ⟨f,hf,hker⟩ := functional_of_codim_one K hKdim
  have hmap : (LinearMap.ker f.toLinearMap).map W.subtype = L := by rw [hker,hKmap]
  have hrestrict : (LinearMap.ker (restrictFunctional hVW f).toLinearMap).map V.subtype = L ⊓ V := by
    rw [restriction_kernel_map,hmap]
  have hfV : restrictFunctional hVW f ≠ 0 := by
    intro hz
    have hh : (LinearMap.ker (restrictFunctional hVW f).toLinearMap).map V.subtype = V := by
      simp [hz]
    have he : L ⊓ V = V := hrestrict.symm.trans hh
    rw [he] at hLVdim
    omega
  have hdV : Dense (restrictFunctional hVW f '' (Λ.comap V.subtype.toAddMonoidHom:Set V)) := by
    apply (native_dense_iff_kernel_not_lambda hΛ _ hfV).mpr
    rwa [hrestrict]
  have hd : Dense (f '' (Λ.comap W.subtype.toAddMonoidHom:Set W)) := by
    rwa [restriction_group_image Λ hVW (native_lattice_subset hΛ) f]
  have hsub : v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ⊆ (W : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro x ⟨y,hy,rfl⟩
    exact W.add_mem hv (hLW hy)
  apply (nativeMaxFree_iff Λ W _ hsub).mpr
  have he : (Subtype.val : W → _) ⁻¹' (v +ᵥ (L:Set _)) = {x:W | f x=f ⟨v,hv⟩} := by
    rw [←hmap]
    exact preimage_vadd_eq_level W f ⟨v,hv⟩
  rw [he]
  exact maxFree_hyperplane_of_dense _ f hf hd _

end MaxLatticeFree.Geometry.Proof
-- End NativeHyperplaneReverse

-- Begin HalfspaceMaximality

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma maxFree_halfspace (Γ : AddSubgroup E) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hΓ : ∀ x ∈ Γ, f x = 0) : MaxFree Γ {x : E | f x ≤ 0} := by
  obtain ⟨e,he⟩ := functional_unit f hf
  have hsur : Function.Surjective f := fun r => ⟨r • e,by simp [he]⟩
  have hint : interior {x : E | f x ≤ 0} = {x : E | f x < 0} := by
    change interior (f ⁻¹' Iic 0) = f ⁻¹' Iio 0
    rw [←(f.isOpenMap hsur).preimage_interior_eq_interior_preimage f.continuous,interior_Iic]
  refine ⟨⟨(convex_Iic 0).linear_preimage f.toLinearMap,?_⟩,?_⟩
  · intro x hx hxΓ
    rw [hint] at hx
    change f x < 0 at hx
    rw [hΓ x hxΓ] at hx
    exact lt_irrefl _ hx
  · intro K hK hsub
    apply Subset.antisymm _ hsub
    intro w hw
    by_contra hn
    have hwpos : 0 < f w := lt_of_not_ge hn
    have hhalf : {z : E | f z < f w / 2} ⊆ K := by
      intro z hz
      change f z < f w / 2 at hz
      have hx : (2:ℝ) • z - w ∈ K := hsub (by
        change f ((2:ℝ) • z - w) ≤ 0
        simp only [map_sub,map_smul,smul_eq_mul]
        linarith)
      have hh := hK.1 hx hw (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num)
        (show (1/2:ℝ)+1/2=1 by norm_num)
      convert hh using 1
      module
    have ho : IsOpen {z : E | f z < f w / 2} := isOpen_lt f.continuous continuous_const
    have hzero : (0:E) ∈ interior K := (ho.subset_interior_iff.mpr hhalf) (by simpa using half_pos hwpos)
    exact hK.2 0 hzero Γ.zero_mem

end MaxLatticeFree.Geometry.Proof
-- End HalfspaceMaximality

-- Begin HalfspaceClassification

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma maxFree_disjoint_subspace_halfspace (Γ : AddSubgroup E) (V : Submodule ℝ E)
    (hΓ : (Γ:Set E) ⊆ (V:Set E)) {S:Set E} (hS : MaxFree Γ S)
    (hi : (interior S).Nonempty) (hdis : Disjoint (interior S) (V:Set E)) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ v ∈ V, f v = 0) ∧ S = {x | f x ≤ 0} := by
  obtain ⟨f,a,hfa,haf⟩ := geometric_hahn_banach_open hS.1.1.interior isOpen_interior V.convex hdis
  have hf : ∀ x ∈ interior S, ∀ v ∈ V, f x < f v := fun x hx v hv => (hfa x hx).trans_le (haf v hv)
  obtain ⟨x,hx⟩ := hi
  have hzero := hf x hx 0 V.zero_mem
  have hfn : f ≠ 0 := by intro he; simp [he] at hzero
  have hV : ∀ v ∈ V, f v = 0 := by
    intro v hv
    by_contra hn
    let t := (f x - 1) / f v
    have hlt := hf x hx (t • v) (V.smul_mem t hv)
    simp only [map_smul,smul_eq_mul] at hlt
    have he : t * f v = f x - 1 := div_mul_cancel₀ _ hn
    linarith
  have hsub : S ⊆ {x | f x ≤ 0} := by
    have hc : closure (interior S) ⊆ {x | f x ≤ 0} := closure_minimal
      (fun y hy => by simpa using (hf y hy 0 V.zero_mem).le)
      (isClosed_le f.continuous continuous_const)
    rw [hS.1.1.closure_interior_eq_closure_of_nonempty_interior ⟨x,hx⟩] at hc
    exact fun y hy => hc (subset_closure hy)
  exact ⟨f,hfn,hV,(hS.2 _ (maxFree_halfspace Γ f hfn (fun v hv => hV v (hΓ hv))).1 hsub).symm⟩

end MaxLatticeFree.Geometry.Proof
-- End HalfspaceClassification

-- Begin NativeHalfspace

open Set
namespace MaxLatticeFree.Geometry.Proof
variable {n : ℕ}

lemma submodule_functional_representation (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (f : W →L[ℝ] ℝ) : ∃ a : EuclideanSpace ℝ (Fin n), ∀ w : W, inner ℝ a (w:EuclideanSpace ℝ (Fin n)) = f w := by
  let a := (InnerProductSpace.toDual ℝ W).symm f
  refine ⟨a,?_⟩
  intro w
  change inner ℝ a w = f w
  exact InnerProductSpace.toDual_symm_apply

lemma native_halfspace_maximal (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (_hVW : V ≤ W) (a : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (ha : ∃ w ∈ W, inner ℝ a w ≠ 0)
    (hV : (V : Set _) ⊆ {x | inner ℝ a x = b}) :
    IsMaxLambdaFree Λ W ((W:Set _) ∩ {x | inner ℝ a x ≤ b}) := by
  have hb : b=0 := by have hh := hV V.zero_mem; simpa using hh.symm
  subst b
  let f : W →L[ℝ] ℝ := (innerSL ℝ a).comp W.subtypeL
  have hf : f ≠ 0 := by
    obtain ⟨w,hw,hn⟩ := ha
    intro he
    have hh := congrArg (fun g : W →L[ℝ] ℝ => g ⟨w,hw⟩) he
    exact hn (by simpa [f] using hh)
  apply (nativeMaxFree_iff Λ W _ inter_subset_left).mpr
  have he : (Subtype.val : W → _) ⁻¹' ((W:Set _) ∩ {x | inner ℝ a x ≤ 0}) = {x : W | f x ≤ 0} := by
    ext x; simp [f]
  rw [he]
  apply maxFree_halfspace _ f hf
  intro x hx
  exact hV (native_lattice_subset hΛ hx)

lemma native_disjoint_halfspace (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (hVW : V ≤ W) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsMaxLambdaFree Λ W S)
    (hi : (intW (W:Set _) S).Nonempty)
    (hdis : Disjoint (intW (W:Set _) S) (V:Set _)) :
    ∃ a : EuclideanSpace ℝ (Fin n), ∃ b : ℝ, (∃ w ∈ W, inner ℝ a w ≠ 0) ∧
      S = (W:Set _) ∩ {x | inner ℝ a x ≤ b} ∧
      (V:Set _) ⊆ {x | inner ℝ a x = b} := by
  let P : Set W := (Subtype.val : W → _) ⁻¹' S
  let U : Submodule ℝ W := V.comap W.subtype
  have hp : MaxFree (Λ.comap W.subtype.toAddMonoidHom) P :=
    (nativeMaxFree_iff Λ W S hS.1.1).mp hS
  have hpi : (interior P).Nonempty := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨⟨x,hS.1.1 hx.1⟩,(intW_subtype_iff (W:Set _) S _).mp hx⟩
  have hpd : Disjoint (interior P) (U:Set W) := by
    apply disjoint_left.mpr
    intro x hx hU
    exact disjoint_left.mp hdis ((intW_subtype_iff (W:Set _) S x).mpr hx) hU
  obtain ⟨f,hf,hU,he⟩ := maxFree_disjoint_subspace_halfspace
    (Λ.comap W.subtype.toAddMonoidHom) U (fun x hx => native_lattice_subset hΛ hx) hp hpi hpd
  obtain ⟨a,ha⟩ := submodule_functional_representation W f
  obtain ⟨w,hw⟩ := functional_unit f hf
  refine ⟨a,0,⟨w,w.property,by rw [ha w,hw]; norm_num⟩,?_,?_⟩
  · ext x
    constructor
    · intro hx
      have hxW := hS.1.1 hx
      refine ⟨hxW,?_⟩
      have hh : (⟨x,hxW⟩:W) ∈ P := hx
      rw [he] at hh
      change inner ℝ a x ≤ 0
      rw [ha ⟨x,hxW⟩]
      exact hh
    · rintro ⟨hxW,hx⟩
      change inner ℝ a x ≤ 0 at hx
      have hh : (⟨x,hxW⟩:W) ∈ {x:W | f x≤0} := by
        change f ⟨x,hxW⟩ ≤ 0
        simpa only [ha ⟨x,hxW⟩] using hx
      rw [←he] at hh
      exact hh
  · intro x hx
    change inner ℝ a x = 0
    rw [ha ⟨x,hVW hx⟩]
    exact hU ⟨x,hVW hx⟩ hx

end MaxLatticeFree.Geometry.Proof
-- End NativeHalfspace

-- Begin RootAssembly

open Pointwise

namespace MaxLatticeFree.Geometry

theorem maxLambdaFree_in_W_iff {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V ≤ W)
    (hW : 0 < Module.finrank ℝ W) (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaxLambdaFree Λ W S ↔
      (IsPolyhedronIn W S ∧ affDim S = (Module.finrank ℝ W : ℤ) ∧
        IsMaxLambdaFree Λ V (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) (F ∩ (V : Set (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
          F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G ∩ (V : Set (EuclideanSpace ℝ (Fin n))) → F = G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) G →
          ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧ F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G)) ∨
      (∃ v ∈ W, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧
        Module.finrank ℝ (L ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ V ∧
        ¬ IsLambdaSubspace Λ V (L ⊓ V)) ∨
      (∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W, inner ℝ a w ≠ 0) ∧
        S = (W : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | inner ℝ a x ≤ b} ∧
        (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ {x | inner ℝ a x = b}) := by
  constructor
  · intro hS
    by_cases hi : intW (W : Set _) S=∅
    · exact Or.inr (Or.inl (Proof.native_empty_interior_hyperplane Λ V W hΛ hVW hW S hS hi))
    · have hne : (intW (W : Set _) S).Nonempty := Set.nonempty_iff_ne_empty.mpr hi
      by_cases hdis : Disjoint (intW (W : Set _) S) (V : Set _)
      · exact Or.inr (Or.inr (Proof.native_disjoint_halfspace Λ V W hΛ hVW S hS hne hdis))
      · have hmeet : ∃ x, x∈intW (W : Set _) S ∧ x∈V := Set.not_disjoint_iff.mp hdis
        exact Or.inl (Proof.native_polyhedral_forward Λ V W hΛ hVW S hS hmeet)
  · rintro (⟨hp,hd,hm,hn,hinj,hs⟩ | ⟨v,hv,L,hLW,hLd,he,hLV,hirr⟩ | ⟨a,b,ha,he,hV⟩)
    · exact Proof.native_polyhedral_reverse Λ V W hΛ hVW S hp hd hm hn hinj hs
    · rw [he]
      exact Proof.native_hyperplane_maximal Λ V W hΛ hVW v hv L hLW hLd hLV hirr
    · rw [he]
      exact Proof.native_halfspace_maximal Λ V W hΛ hVW a b ha hV

end MaxLatticeFree.Geometry
-- End RootAssembly

-- Begin Solution

open Pointwise MaxLatticeFree.Geometry

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hVW : V ≤ W)
    (hW : 0 < Module.finrank ℝ W) (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaxLambdaFree Λ W S ↔
      (IsPolyhedronIn W S ∧ affDim S = (Module.finrank ℝ W : ℤ) ∧
        IsMaxLambdaFree Λ V (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) (F ∩ (V : Set (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
          F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G ∩ (V : Set (EuclideanSpace ℝ (Fin n))) → F = G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsFacet (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) G →
          ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧ F ∩ (V : Set (EuclideanSpace ℝ (Fin n))) = G)) ∨
      (∃ v ∈ W, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧
        Module.finrank ℝ (L ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ V ∧
        ¬ IsLambdaSubspace Λ V (L ⊓ V)) ∨
      (∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W, inner ℝ a w ≠ 0) ∧
        S = (W : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | inner ℝ a x ≤ b} ∧
        (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ {x | inner ℝ a x = b}) := by
  exact MaxLatticeFree.Geometry.maxLambdaFree_in_W_iff Λ V W hΛ hVW hW S
-- End Solution
