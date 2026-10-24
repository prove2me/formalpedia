-- Prove2me | solution 1 for MaxLatticeFree.Geometry.lovasz_maxLambdaFree_iff
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:34:18.573551+00:00
-- url     : https://prove2.me/submissions/99e3dde6-97cd-45d8-895b-94e728729e7e

-- Licensed under Apache 2.0.
-- Selected complete proof blocks are adapted from the accepted submission of
-- MaxLatticeFree.Geometry.maxLambdaFree_in_W_iff by the external source author.
-- Source submission fe37f171-6a7a-45e8-b259-ee963587c72a;
-- original source SHA256 04632fd6a8856672e97a5697f3826a0ca2ead527b000f4e91b4d4d24858c582f.
-- Blocks retain complete proofs; namespace renaming and a local rfl unfolding
-- lemma avoid relying on an imported generated equation theorem.
-- The finite-hull bridge is copied from the checked lattice-polytope task,
-- FiniteHull.lean SHA256 2ac0dbfe844cc80eb4deffd2189634aab951afd2dd3be2e7e04d7a53d45a888b.
import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Theorems.Thm_MaxLatticeFree_Geometry_maxLambdaFree_in_W_iff
import Theorems.Thm_MaxLatticeFree_Geometry_unbounded_maxLambdaFree_linSpace_eq_recCone
import Theorems.Thm_MaxLatticeFree_Geometry_unbounded_maxLambdaFree_linSpace_isLambdaSubspace
import Theorems.Thm_MaxLatticeFree_Geometry_hyperplane_maxLambdaFree_iff

namespace MaxLatticeFree.Geometry
open Classical in
lemma classification_affDim_unfold {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    affDim S = if S.Nonempty then (Module.finrank ℝ (affineSpan ℝ S).direction : ℤ) else -1 := rfl
end MaxLatticeFree.Geometry


-- Begin PolyBody

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

def polyBody (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}

lemma polyBody_convex (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (polyBody a b) := by
  intro x hx y hy s t hs ht hsum i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    s*a i x+t*a i y ≤ s*b i+t*b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul,hsum,one_mul]

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyBody

-- Begin PolyTopology

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyTopology

-- Begin PolyInterior

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyInterior

-- Begin PolyCoercive

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyCoercive

-- Begin PolyFinite

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyFinite

-- Begin IrredundantSystem

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End IrredundantSystem

-- Begin StrictFacePoint

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End StrictFacePoint

-- Begin FiniteSlack

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FiniteSlack

-- Begin RowFaceSpan

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End RowFaceSpan

-- Begin PolyStrictSelection

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyStrictSelection

-- Begin GenericFacet

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End GenericFacet

-- Begin SubtypeDimension

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma direction_rank_subtype_image (W : Submodule ℝ E) (S : Set W) :
    Module.finrank ℝ (affineSpan ℝ (Subtype.val '' S : Set E)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have he : (Subtype.val '' S : Set E) = W.subtype.toAffineMap '' S := rfl
  rw [he,← AffineSubspace.map_span,AffineSubspace.map_direction]
  exact Submodule.finrank_map_subtype_eq W _

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End SubtypeDimension

-- Begin NativeFacet

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

variable {n : ℕ}

lemma nativeFacet_iff_gFacet (S F : Set (EuclideanSpace ℝ (Fin n))) :
    IsFacet S F ↔ GFacet S F := by
  constructor
  · rintro ⟨hne,hd,a,b,hb,he⟩
    have hS : S.Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,(show x∈S ∩ {x | inner ℝ a x=b} from he ▸ hx).1⟩
    refine ⟨hne,?_,(innerSL ℝ a).toLinearMap,b,hb,he⟩
    simp only [classification_affDim_unfold,if_pos hne,if_pos hS] at hd
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
    · simp only [classification_affDim_unfold,if_pos hne,if_pos hS]
      omega
    · intro x hx
      rw [ha]
      exact hb x hx
    · simpa only [ha] using he

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativeFacet

-- Begin NativeInterior

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativeInterior

-- Begin GenericFree

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Interior lattice-freeness in the space currently under consideration. -/
def Free (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Convex ℝ S ∧ ∀ x ∈ interior S, x ∉ Γ

/-- Maximality among convex sets free of the specified additive subgroup. -/
def MaxFree (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Free Γ S ∧ ∀ K : Set E, Free Γ K → S ⊆ K → K = S

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End GenericFree

-- Begin NativeFree

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativeFree

-- Begin SubtypeFacet

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End SubtypeFacet

-- Begin NativePolyhedron

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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
      simp only [classification_affDim_unfold,if_neg hn] at hd
      omega
    have hPne : P.Nonempty := image_nonempty.mp (himg.symm ▸ hne)
    have hdNat : Module.finrank ℝ (affineSpan ℝ P).direction=Module.finrank ℝ W := by
      simp only [classification_affDim_unfold,if_pos hne] at hd
      rw [hrank] at hd
      omega
    have hdir : (affineSpan ℝ P).direction=⊤ := Submodule.eq_top_of_finrank_eq hdNat
    exact hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
      ((AffineSubspace.direction_eq_top_iff_of_nonempty (hPne.affineSpan ℝ)).mp hdir)
  · intro hi
    have hPne : P.Nonempty := hi.mono interior_subset
    have hne : S.Nonempty := himg ▸ hPne.image Subtype.val
    simp only [classification_affDim_unfold,if_pos hne]
    rw [hrank,hconv.interior_nonempty_iff_affineSpan_eq_top.mp hi,
      AffineSubspace.direction_top,finrank_top]

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativePolyhedron

-- Begin HyperplaneGeometry

open Set Metric
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End HyperplaneGeometry

-- Begin KernelSpan

open Set
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End KernelSpan

-- Begin DiscreteFinite

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End DiscreteFinite

-- Begin KernelRounding

open Set Metric
open scoped BigOperators
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End KernelRounding

-- Begin LatticeDiscrete

open Set Metric
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End LatticeDiscrete

-- Begin LatticeSpanAdapters

open Set
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End LatticeSpanAdapters

-- Begin RationalKernel

open Set
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End RationalKernel

-- Begin NativeLatticeAdapters

open Set
namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativeLatticeAdapters

-- Begin FreeEquiv

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FreeEquiv

-- Begin NativeNested

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End NativeNested

-- Begin FreeGeometry

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FreeGeometry

-- Begin RecessionBasic

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End RecessionBasic

-- Begin OrthogonalSlice

open Set
open scoped Pointwise Topology
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End OrthogonalSlice

-- Begin TorusApproximation

open Set Filter
open scoped BigOperators Topology
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End TorusApproximation

-- Begin RecessionFree

open Set Metric
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End RecessionFree

-- Begin RecessionBounded

open Set Filter Metric
open scoped Topology
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End RecessionBounded

-- Begin GroupClosureLine

open Set Filter Metric
open scoped Topology
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End GroupClosureLine

-- Begin BoundedFreeDiscrete

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End BoundedFreeDiscrete

-- Begin BoundedQuotient

open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationImportedProof
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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End BoundedQuotient

-- Begin SupportingFunctional

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End SupportingFunctional

-- Begin BoundedPolyhedral

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End BoundedPolyhedral

-- Begin PolyRecession

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End PolyRecession

-- Begin FacetLatticePoint

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FacetLatticePoint

-- Begin FullPolyhedral

open Set

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FullPolyhedral

-- Begin FacetMaximality

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.ClassificationImportedProof

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

end MaxLatticeFree.Geometry.ClassificationImportedProof
-- End FacetMaximality


-- Local module RelativeGeometry


namespace MaxLatticeFree.Geometry.ClassificationProof

lemma intW_subtype {n : ℕ} (W C : Set (EuclideanSpace ℝ (Fin n))) (hCW : C ⊆ W) :
    intW W C = (Subtype.val : W → EuclideanSpace ℝ (Fin n)) ''
      interior ((Subtype.val : W → EuclideanSpace ℝ (Fin n)) ⁻¹' C) := by
  ext x
  constructor
  · rintro ⟨hx, ε, hε, hball⟩
    refine ⟨⟨x, hCW hx⟩, ?_, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply Metric.mem_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro y hy
    exact hball ⟨hy, y.property⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨show x ∈ (Subtype.val : W → EuclideanSpace ℝ (Fin n)) ⁻¹' C from interior_subset hx, ε, hε, ?_⟩
    rintro y ⟨hy, hyW⟩
    exact hball (show (⟨y, hyW⟩ : W) ∈ Metric.ball x ε from hy)

lemma intW_mono {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n)))
    {C S : Set (EuclideanSpace ℝ (Fin n))} (hCS : C ⊆ S) : intW W C ⊆ intW W S := by
  rintro x ⟨hx, ε, hε, hball⟩
  exact ⟨hCS hx, ε, hε, hball.trans hCS⟩


lemma affineSpan_eq_of_full_dim {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hne : S.Nonempty)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    affineSpan ℝ S = V.toAffineSubspace := by
  have hle : affineSpan ℝ S ≤ V.toAffineSubspace := affineSpan_le.mpr hSV
  have hdir : (affineSpan ℝ S).direction ≤ V := by
    simpa only [Submodule.toAffineSubspace_direction] using AffineSubspace.direction_le hle
  have hfin : Module.finrank ℝ (affineSpan ℝ S).direction = Module.finrank ℝ V := by
    simp only [classification_affDim_unfold, if_pos hne] at hdim
    exact_mod_cast hdim
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ (hne.affineSpan ℝ) hle
  simpa only [Submodule.toAffineSubspace_direction] using Submodule.eq_of_le_of_finrank_eq hdir hfin

lemma interior_subtype_nonempty_of_full_dim {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hS : Convex ℝ S)
    (hne : S.Nonempty) (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    (interior ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S)).Nonempty := by
  have hspan := affineSpan_eq_of_full_dim V S hSV hne hdim
  have hInt := hne.intrinsicInterior hS
  unfold intrinsicInterior at hInt
  rw [hspan] at hInt
  exact Set.image_nonempty.mp hInt

lemma intW_nonempty_of_full_dim {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSV : S ⊆ V) (hS : Convex ℝ S)
    (hne : S.Nonempty) (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    (intW (V : Set _) S).Nonempty := by
  rw [intW_subtype _ _ hSV, Set.image_nonempty]
  exact interior_subtype_nonempty_of_full_dim V S hSV hS hne hdim

end MaxLatticeFree.Geometry.ClassificationProof


-- Local module ProjectionBasics


open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationProof

lemma polyhedron_isClosed {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsPolyhedronIn V S) : IsClosed S := by
  obtain ⟨m, a, b, rfl⟩ := hS
  apply V.closed_of_finiteDimensional.inter
  have heq : {x | ∀ i, inner ℝ (a i) x ≤ b i} = ⋂ i, {x | inner ℝ (a i) x ≤ b i} := by
    ext x
    simp
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma add_mem_of_linSpace {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (hv : v ∈ L) : x+v ∈ S := by
  have hv' : v ∈ linSpace S := hL ▸ hv
  simpa only [one_smul] using hv'.1 x hx 1 zero_le_one

lemma projection_mem {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) : Lᗮ.starProjection x ∈ S := by
  have hv : x - Lᗮ.starProjection x ∈ L := by
    simpa only [Submodule.orthogonal_orthogonal] using Lᗮ.sub_starProjection_mem_orthogonal x
  have h := add_mem_of_linSpace L hL hx (L.neg_mem hv)
  convert h using 1
  abel

lemma projection_eq_inter {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S) :
    Lᗮ.starProjection '' S = S ∩ (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨projection_mem L hL hy, Lᗮ.starProjection_apply_mem y⟩
  · intro hx
    exact ⟨x, hx.1, (Submodule.starProjection_eq_self_iff).mpr hx.2⟩

lemma projection_decomposition {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S) :
    S = (Lᗮ.starProjection '' S) + (L : Set (EuclideanSpace ℝ (Fin n))) := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨Lᗮ.starProjection x, ⟨x, hx, rfl⟩, x-Lᗮ.starProjection x, ?_, by abel_nf⟩
    change x - Lᗮ.starProjection x ∈ L
    simpa only [Submodule.orthogonal_orthogonal] using Lᗮ.sub_starProjection_mem_orthogonal x
  · rintro x ⟨p, ⟨y, hy, rfl⟩, v, hv, rfl⟩
    exact add_mem_of_linSpace L hL (projection_mem L hL hy) hv

lemma projection_bounded_of_recession_eq_lineality {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Convex ℝ S) (hclosed : IsClosed S)
    (hne : S.Nonempty) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S)
    (hrec : linSpace S = recCone S) : Bornology.IsBounded (Lᗮ.starProjection '' S) := by
  let P := Lᗮ.starProjection '' S
  have hPclosed : IsClosed P := by
    rw [show P = Lᗮ.starProjection '' S from rfl, projection_eq_inter L hL]
    exact hclosed.inter Lᗮ.closed_of_finiteDimensional
  have hPconv : Convex ℝ P := hS.linear_image Lᗮ.starProjection.toLinearMap
  have hPne : P.Nonempty := hne.image Lᗮ.starProjection
  by_contra hbound
  obtain ⟨r, hr0, hr⟩ := not_bounded_iff_exists_ne_zero_mem_asymptoticCone.mp hbound
  have hrP : r ∈ recCone P := by
    intro x hx t ht
    simpa only [vadd_eq_add, add_comm] using
      hPconv.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hPclosed ht hr hx
  have hrS : r ∈ recCone S := by
    intro x hx t ht
    rw [projection_decomposition L hL] at hx ⊢
    obtain ⟨p, hp, v, hv, rfl⟩ := hx
    exact ⟨p+t•r, hrP p hp t ht, v, hv, by dsimp; ac_rfl⟩
  have hrL : r ∈ L := by
    change r ∈ (L : Set (EuclideanSpace ℝ (Fin n)))
    rw [hL, hrec]
    exact hrS
  have hrO : r ∈ Lᗮ := by
    obtain ⟨p, hp⟩ := hPne
    have hp' : p ∈ Lᗮ := by
      change p ∈ Lᗮ.starProjection '' S at hp
      rw [projection_eq_inter L hL] at hp
      exact hp.2
    have hpr : p+r ∈ Lᗮ := by
      have h := hrP p hp 1 zero_le_one
      rw [show P = Lᗮ.starProjection '' S from rfl, projection_eq_inter L hL] at h
      have hh := h.2
      change p + 1 • r ∈ Lᗮ at hh
      simpa only [one_smul] using hh
    simpa only [add_sub_cancel_left] using Lᗮ.sub_mem hpr hp'
  exact hr0 (inner_self_eq_zero.mp (L.inner_right_of_mem_orthogonal hrL hrO))

end MaxLatticeFree.Geometry.ClassificationProof


-- Local module FacetBridge


open Set Filter
open scoped Topology
namespace MaxLatticeFree.Geometry.ClassificationProof
open MaxLatticeFree.Geometry.ClassificationImportedProof

lemma strict_of_intrinsicInterior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) (b : ℝ) (F : Set E)
    (hbound : ∀ x ∈ F, f x ≤ b) {z y : E} (hz : z ∈ intrinsicInterior ℝ F)
    (hy : y ∈ F) (hylt : f y < b) : f z < b := by
  obtain ⟨z', hz', rfl⟩ := hz
  let : Nonempty (affineSpan ℝ F) := ⟨z'⟩
  let y' : affineSpan ℝ F := ⟨y, subset_affineSpan ℝ F hy⟩
  have hcont : Continuous (fun t : ℝ => t • (z' -ᵥ y') +ᵥ z') := by fun_prop
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ((t • (z' -ᵥ y') +ᵥ z' : affineSpan ℝ F) : E) ∈ F := by
    have hn : ((Subtype.val : affineSpan ℝ F → E) ⁻¹' F) ∈
        𝓝 ((0 : ℝ) • (z' -ᵥ y') +ᵥ z') := by
      simpa only [zero_smul, zero_vadd] using mem_interior_iff_mem_nhds.mp hz'
    exact (hcont.tendsto 0).eventually (show ∀ᶠ x : affineSpan ℝ F in
      𝓝 ((0 : ℝ) • (z' -ᵥ y') +ᵥ z'), (x : E) ∈ F from hn)
  obtain ⟨t, ht, htF⟩ := hevent.exists_gt
  have hzt : f ((t • (z' -ᵥ y') +ᵥ z' : affineSpan ℝ F) : E) ≤ b := hbound _ htF
  have hzle : f (z' : E) ≤ b := hbound _ (show z' ∈ (Subtype.val : affineSpan ℝ F → E) ⁻¹' F from interior_subset hz')
  change f (t • ((z' : E) - y) + (z' : E)) ≤ b at hzt
  rw [map_add, map_smul, map_sub] at hzt
  change t * (f (z' : E) - f y) + f (z' : E) ≤ b at hzt
  by_contra hn
  have heq : f (z' : E) = b := le_antisymm hzle (le_of_not_gt hn)
  rw [heq] at hzt
  have hp := mul_pos ht (sub_pos.mpr hylt)
  linarith

lemma strict_point_mem_intrinsicInterior_rowFace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι) {z : E}
    (hz : a i z = b i) (hstrict : ∀ j, j ≠ i → a j z < b j) :
    z ∈ intrinsicInterior ℝ (rowFace a b i) := by
  classical
  have hzF : z ∈ rowFace a b i := by
    refine ⟨?_, hz⟩
    intro j
    by_cases hj : j=i
    · simpa [hj] using hz.le
    · exact (hstrict j hj).le
  let Z := affineSpan ℝ (rowFace a b i)
  let z' : Z := ⟨z, subset_affineSpan ℝ _ hzF⟩
  have hspan : Z ≤ AffineSubspace.mk' z (LinearMap.ker (a i)) := by
    apply affineSpan_le.mpr
    intro x hx
    change a i (x-z)=0
    rw [map_sub,hx.2,hz,sub_self]
  have hactive (x : Z) : a i x = b i := by
    have hx := hspan x.property
    change a i ((x : E)-z)=0 at hx
    rw [map_sub,hz] at hx
    linarith
  refine ⟨z', mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  have hevent : ∀ j, ∀ᶠ x : Z in 𝓝 z', j≠i → a j x < b j := by
    intro j
    by_cases hj : j=i
    · exact Eventually.of_forall fun _ h => (h hj).elim
    · have hc : Continuous (fun x : Z => a j x) :=
        (a j).continuous_of_finiteDimensional.comp continuous_subtype_val
      filter_upwards [(hc.tendsto z').eventually (gt_mem_nhds (hstrict j hj))] with x hx
      exact fun _ => hx
  filter_upwards [eventually_all.mpr hevent] with x hx
  refine ⟨?_, hactive x⟩
  intro j
  by_cases hj : j=i
  · simpa [hj] using (hactive x).le
  · exact (hx j hj).le

lemma full_maxFree_facet_points {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Γ : AddSubgroup E)
    (hspan : Submodule.span ℝ (Γ : Set E)=⊤) {S : Set E}
    (hS : MaxFree Γ S) (hint : (interior S).Nonempty) :
    ∀ F, GFacet S F → ∃ z ∈ Γ, z ∈ intrinsicInterior ℝ F := by
  obtain ⟨t,a,b,he,hw,hz⟩ := full_maxFree_system Γ hspan hS hint
  subst S
  intro F hF
  obtain ⟨i,rfl⟩ := gFacet_eq_rowFace a b hint hw hF
  obtain ⟨z,hzΓ,hzi,hzothers⟩ := hz i
  exact ⟨z,hzΓ,strict_point_mem_intrinsicInterior_rowFace a b i hzi hzothers⟩

lemma maxFree_of_polyhedral_facets {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Γ : AddSubgroup E) {S : Set E}
    (hpoly : Polyhedral S) (hint : (interior S).Nonempty) (hfree : Free Γ S)
    (hfacet : ∀ F, GFacet S F → ∃ z ∈ Γ, z ∈ intrinsicInterior ℝ F) : MaxFree Γ S := by
  obtain ⟨t,a,b,he,hw⟩ := polyhedral_irredundant hpoly
  subst S
  apply system_lattice_points_maxFree Γ a b hfree
  intro i
  obtain ⟨z,hzΓ,hz⟩ := hfacet (rowFace a b i) (rowFace_is_gFacet a b hint hw i)
  have hzF := intrinsicInterior_subset hz
  refine ⟨z,hzΓ,hzF.2,?_⟩
  intro j hji
  obtain ⟨w,hwi,hwothers⟩ := exists_strict_face_point a b hint hw i
  have hwF : w ∈ rowFace a b i := by
    refine ⟨?_,hwi⟩
    intro k
    by_cases hki : k=i
    · simpa [hki] using hwi.le
    · exact (hwothers k hki).le
  exact strict_of_intrinsicInterior (a j) (b j) (rowFace a b i)
    (fun x hx => hx.1 j) hz hwF (hwothers j hji)

end MaxLatticeFree.Geometry.ClassificationProof


-- Local module FiniteHull


open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.ClassificationProof
open MaxLatticeFree.Geometry.ClassificationImportedProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- Active inequalities determine an extreme point of a finite halfspace system. -/
lemma extreme_eq_of_active (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {x y : E} (hx : x ∈ (polyBody a b).extremePoints ℝ)
    (hy : y ∈ polyBody a b) (hactive : ∀ i, a i x = b i → a i y = b i) : x = y := by
  have hd : ∀ i, a i x = b i → a i (x - y) ≤ 0 := by
    intro i hi
    simp [map_sub, hi, hactive i hi]
  obtain ⟨t, ht, hz⟩ := feasible_direction_step hx.1 hd
  have ht1 : 0 < 1 + t := by linarith
  have he : t / (1 + t) + 1 / (1 + t) = (1 : ℝ) := by field_simp; ring
  have hseg : x ∈ openSegment ℝ y (x + t • (x-y)) := by
    refine ⟨t / (1+t), 1 / (1+t), div_pos ht ht1, div_pos zero_lt_one ht1, he, ?_⟩
    have hcoef : (1 / (1+t)) * t = t / (1+t) := by ring
    simp only [smul_add, smul_sub, smul_smul, hcoef]
    calc
      (t / (1+t)) • y + ((1 / (1+t)) • x +
          ((t / (1+t)) • x - (t / (1+t)) • y)) =
          (t / (1+t)) • x + (1 / (1+t)) • x := by abel
      _ = x := by rw [← add_smul, he, one_smul]
  exact (hx.2 hy hz hseg).symm

omit [FiniteDimensional ℝ E] in
lemma polyBody_extremePoints_finite (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    ((polyBody a b).extremePoints ℝ).Finite := by
  classical
  let active : E → Set ι := fun x => {i | a i x = b i}
  have hinj : Set.InjOn active ((polyBody a b).extremePoints ℝ) := by
    intro x hx y hy he
    apply extreme_eq_of_active a b hx hy.1
    intro i hi
    exact (Set.ext_iff.mp he i).mp hi
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

lemma bounded_polyBody_finite_hull (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded (polyBody a b)) :
    ∃ F : Finset E, polyBody a b = convexHull ℝ (F : Set E) := by
  classical
  have hf := polyBody_extremePoints_finite a b
  have hc : IsCompact (polyBody a b) :=
    Metric.isCompact_of_isClosed_isBounded (polyBody_closed a b) hb
  refine ⟨hf.toFinset, ?_⟩
  rw [hf.coe_toFinset]
  have he := closure_convexHull_extremePoints hc (polyBody_convex a b)
  rw [(hf.isCompact_convexHull ℝ).isClosed.closure_eq] at he
  exact he.symm

end MaxLatticeFree.Geometry.ClassificationProof


-- Local module NativeBridge


open Set
open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationProof
open MaxLatticeFree.Geometry.ClassificationImportedProof

lemma bounded_polyhedron_isPolytope {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hpoly : IsPolyhedronIn V S)
    (hb : Bornology.IsBounded S) : IsPolytope S := by
  classical
  have hSV : S ⊆ (V : Set _) := by
    obtain ⟨t,a,b,he⟩ := hpoly
    rw [he]
    exact inter_subset_left
  obtain ⟨t,a,b,he⟩ := (nativePolyhedron_iff V S hSV).mp hpoly
  have hb' : Bornology.IsBounded ((Subtype.val : V → _) ⁻¹' S) :=
    isometry_subtype_coe.antilipschitz.isBounded_preimage hb
  obtain ⟨F,hF⟩ := bounded_polyBody_finite_hull a b (he ▸ hb')
  refine ⟨F.image (Subtype.val : V → _), ?_⟩
  rw [Finset.coe_image]
  change S = convexHull ℝ (V.subtype '' (F : Set V))
  rw [← V.subtype.image_convexHull]
  rw [← hF, ← he]
  exact (subtype_image_preimage_of_subset V S hSV).symm

lemma native_full_facet_points {n : ℕ}
    (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hd : affDim S = (Module.finrank ℝ V : ℤ)) :
    ∀ F, IsFacet S F → ∃ z ∈ Λ, z ∈ relint F := by
  intro F hF
  have hFV : F ⊆ (V : Set _) := by
    obtain ⟨_,_,a,b,_,he⟩ := hF
    rw [he]
    exact inter_subset_left.trans hS.1.1
  have hFg := (nativeFacet_subtype_iff V S F hS.1.1 hFV).mp hF
  obtain ⟨z,hzΛ,hz⟩ := full_maxFree_facet_points (Λ.comap V.subtype.toAddMonoidHom)
    (native_lattice_comap_span hΛ) ((nativeMaxFree_iff Λ V S hS.1.1).mp hS)
    ((nativeFullDim_iff V S hS.1.1 hS.1.2.1).mp hd) _ hFg
  refine ⟨z,hzΛ,?_⟩
  rw [relint_eq_intrinsicInterior, ← subtype_image_preimage_of_subset V F hFV]
  have he := V.subtypeₗᵢ.toAffineIsometry.intrinsicInterior_image
    ((Subtype.val : V → _) ⁻¹' F)
  change intrinsicInterior ℝ (Subtype.val '' ((Subtype.val : V → _) ⁻¹' F)) =
    Subtype.val '' intrinsicInterior ℝ ((Subtype.val : V → _) ⁻¹' F) at he
  rw [he]
  exact ⟨z,hz,rfl⟩

lemma native_maximal_of_polyhedral_facets {n : ℕ}
    (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hpoly : IsPolyhedronIn V S)
    (hd : affDim S = (Module.finrank ℝ V : ℤ))
    (hfree : (Λ : Set _) ∩ intW (V : Set _) S = ∅)
    (hfacet : ∀ F, IsFacet S F → ∃ z ∈ Λ, z ∈ relint F) :
    IsMaxLambdaFree Λ V S := by
  have hSV : S ⊆ (V : Set _) := by
    obtain ⟨t,a,b,he⟩ := hpoly
    rw [he]
    exact inter_subset_left
  have hc : Convex ℝ S := by
    obtain ⟨t,a,b,rfl⟩ := hpoly
    apply V.convex.inter
    rw [Set.ofPred_forall]
    apply convex_iInter
    intro i
    exact convex_halfSpace_le (innerSL ℝ (a i)).toLinearMap.isLinear (b i)
  apply (nativeMaxFree_iff Λ V S hSV).mpr
  apply maxFree_of_polyhedral_facets (Λ.comap V.subtype.toAddMonoidHom)
    ((nativePolyhedron_iff V S hSV).mp hpoly)
    ((nativeFullDim_iff V S hSV hc).mp hd)
    ((nativeFree_iff Λ V S hSV).mp ⟨hSV,hc,hfree⟩)
  intro F hF
  have hF' : IsFacet S (Subtype.val '' F) := by
    rw [nativeFacet_iff_gFacet, ← subtype_image_preimage_of_subset V S hSV]
    exact (gFacet_subtype_image_iff V _ F).mpr hF
  obtain ⟨z,hzΛ,hz⟩ := hfacet _ hF'
  rw [relint_eq_intrinsicInterior] at hz
  have he := V.subtypeₗᵢ.toAffineIsometry.intrinsicInterior_image F
  change intrinsicInterior ℝ (Subtype.val '' F) =
    Subtype.val '' intrinsicInterior ℝ F at he
  rw [he] at hz
  obtain ⟨w,hw,rfl⟩ := hz
  exact ⟨w,hzΛ,hw⟩

lemma projection_polyhedral {n : ℕ} (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hpoly : IsPolyhedronIn V S)
    (hL : (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S) :
    IsPolyhedronIn (Lᗮ ⊓ V) (Lᗮ.starProjection '' S) := by
  rw [projection_eq_inter L hL]
  obtain ⟨t,a,b,rfl⟩ := hpoly
  refine ⟨t,a,b,?_⟩
  ext x
  simp only [mem_inter_iff, Submodule.mem_inf, SetLike.mem_coe, mem_ofPred_eq]
  tauto

lemma projection_affineSpan {n : ℕ} (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hLV : L ≤ V) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hspan : affineSpan ℝ S = V.toAffineSubspace) :
    affineSpan ℝ (Lᗮ.starProjection '' S) = (Lᗮ ⊓ V).toAffineSubspace := by
  change affineSpan ℝ (Lᗮ.starProjection.toLinearMap.toAffineMap '' S) = _
  rw [← AffineSubspace.map_span Lᗮ.starProjection.toLinearMap.toAffineMap, hspan]
  ext x
  change (∃ y ∈ V, Lᗮ.starProjection y = x) ↔ x ∈ Lᗮ ⊓ V
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨Lᗮ.starProjection_apply_mem y, ?_⟩
    have hsub : y - Lᗮ.starProjection y ∈ L := by
      simpa only [Submodule.orthogonal_orthogonal] using Lᗮ.sub_starProjection_mem_orthogonal y
    change Lᗮ.starProjection y ∈ V
    convert V.sub_mem hy (hLV hsub) using 1
    abel
  · intro hx
    exact ⟨x,hx.2,Submodule.starProjection_eq_self_iff.mpr hx.1⟩

end MaxLatticeFree.Geometry.ClassificationProof


-- Local module Assembly


open scoped Pointwise
namespace MaxLatticeFree.Geometry.ClassificationProof
lemma bottom_lambdaSubspace {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : IsLambdaSubspace Λ V ⊥ := by
  refine ⟨bot_le, 0, (fun i : Fin 0 => Fin.elim0 i), ?_, ?_, ?_⟩
  · exact linearIndependent_empty_type
  · simp
  · intro i
    exact Fin.elim0 i
end MaxLatticeFree.Geometry.ClassificationProof

namespace MaxLatticeFree.Geometry

theorem _root_.solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hV : 0 < Module.finrank ℝ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaxLambdaFree Λ V S ↔
      (IsPolyhedronIn V S ∧
        ∃ (P : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
          IsPolytope P ∧ IsLambdaSubspace Λ V L ∧ S = P + (L : Set (EuclideanSpace ℝ (Fin n))) ∧
          affDim S = affDim P + (Module.finrank ℝ L : ℤ) ∧
          affDim P + (Module.finrank ℝ L : ℤ) = (Module.finrank ℝ V : ℤ) ∧
          (Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ intW (V : Set (EuclideanSpace ℝ (Fin n))) S = ∅ ∧
          ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → ∃ x ∈ Λ, x ∈ relint F) ∨
      (∃ v ∈ V, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ V ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ V ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧ ¬ IsLambdaSubspace Λ V L) := by
  constructor
  · intro hS
    have hcases := (maxLambdaFree_in_W_iff Λ V V hΛ le_rfl hV S).mp hS
    rcases hcases with hfull | hhyper | hhalf
    · rcases hfull with ⟨hpoly,hd,_,_,_,_⟩
      left
      refine ⟨hpoly, ?_⟩
      have hfacet := ClassificationProof.native_full_facet_points Λ V hΛ S hS hd
      by_cases hb : Bornology.IsBounded S
      · refine ⟨S,⊥, ClassificationProof.bounded_polyhedron_isPolytope V S hpoly hb,
          ClassificationProof.bottom_lambdaSubspace Λ V, ?_, ?_, ?_, hS.1.2.2, hfacet⟩
        · simp
        · simp
        · simpa using hd
      · obtain ⟨L,hL,hLΛ⟩ := unbounded_maxLambdaFree_linSpace_isLambdaSubspace Λ V hΛ S hS hd hb
        have hrec := unbounded_maxLambdaFree_linSpace_eq_recCone Λ V hΛ S hS hd hb
        have hne : S.Nonempty := by
          by_contra hn
          simp only [classification_affDim_unfold,if_neg hn] at hd
          omega
        let P := Lᗮ.starProjection '' S
        have hPpoly := ClassificationProof.projection_polyhedral V L hpoly hL
        have hPb := ClassificationProof.projection_bounded_of_recession_eq_lineality S
          hS.1.2.1 (ClassificationProof.polyhedron_isClosed V hpoly) hne L hL hrec
        have hPspan : affineSpan ℝ P = (Lᗮ ⊓ V).toAffineSubspace :=
          ClassificationProof.projection_affineSpan V L hLΛ.1
            (ClassificationProof.affineSpan_eq_of_full_dim V S hS.1.1 hne hd)
        have hPdim : affDim P = (Module.finrank ℝ (Lᗮ ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℤ) := by
          rw [classification_affDim_unfold, if_pos (hne.image _), hPspan, Submodule.toAffineSubspace_direction]
        have hsum : affDim P + (Module.finrank ℝ L : ℤ) = (Module.finrank ℝ V : ℤ) := by
          rw [hPdim]
          have hh := Submodule.finrank_add_inf_finrank_orthogonal hLΛ.1
          omega
        exact ⟨P,L,ClassificationProof.bounded_polyhedron_isPolytope _ P hPpoly hPb,hLΛ,
          ClassificationProof.projection_decomposition L hL,hd.trans hsum.symm,hsum,hS.1.2.2,hfacet⟩
    · right
      obtain ⟨v,hv,L,hLV,hd,he,_,hirr⟩ := hhyper
      refine ⟨v,hv,L,hLV,hd,he,?_⟩
      simpa only [inf_eq_left.mpr hLV] using hirr
    · obtain ⟨a,b,⟨w,hw,hwne⟩,_,hlevel⟩ := hhalf
      have hb : b=0 := by simpa using (hlevel V.zero_mem).symm
      have hw0 := hlevel hw
      exact (hwne (hb ▸ hw0)).elim
  · rintro (⟨hpoly,P,L,_,_,_,hd,hsum,hfree,hfacet⟩ | ⟨v,hv,L,hLV,hd,rfl,hirr⟩)
    · exact ClassificationProof.native_maximal_of_polyhedral_facets Λ V S hpoly
        (hd.trans hsum) hfree hfacet
    · exact (hyperplane_maxLambdaFree_iff Λ V hΛ L hLV hd v hv).mpr hirr

end MaxLatticeFree.Geometry
