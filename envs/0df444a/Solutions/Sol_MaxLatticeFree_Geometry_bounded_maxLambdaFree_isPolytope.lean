-- Prove2me | solution 1 for MaxLatticeFree.Geometry.bounded_maxLambdaFree_isPolytope
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:22:47.439595+00:00
-- url     : https://prove2.me/submissions/5763b736-e3e3-4cf9-a237-e89d50fb1241

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron

/- Complete proof bodies from AcceptedHelpers.lean. -/
/-
Adapted proof blocks from the accepted proof of MaxLatticeFree.Geometry.maxLambdaFree_in_W_iff,
submission fe37f171-6a7a-45e8-b259-ee963587c72a (theorem 30501371-1d31-4527-ab62-c969477d7128).
Original source says: "Complete checked reconstruction of the native three-case maximal lattice-free
classification. Licensed under Apache 2.0." Retained under Apache 2.0.
Only required blocks are included, with their namespace renamed to PolytopeProof to avoid collisions.
Original accepted bytes and block/source hashes are recorded in source/ and helper-provenance.json.
-/

-- Begin accepted block: PolyBody

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

def polyBody (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}

lemma polyBody_convex (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Convex ℝ (polyBody a b) := by
  intro x hx y hy s t hs ht hsum i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    s*a i x+t*a i y ≤ s*b i+t*b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul,hsum,one_mul]

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyBody

-- Begin accepted block: PolyTopology

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyTopology

-- Begin accepted block: PolyInterior

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyInterior

-- Begin accepted block: PolyCoercive

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyCoercive

-- Begin accepted block: PolyFinite

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyFinite

-- Begin accepted block: IrredundantSystem

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: IrredundantSystem

-- Begin accepted block: StrictFacePoint

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: StrictFacePoint

-- Begin accepted block: FiniteSlack

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: FiniteSlack

-- Begin accepted block: RowFaceSpan

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: RowFaceSpan

-- Begin accepted block: PolyStrictSelection

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyStrictSelection

-- Begin accepted block: GenericFacet

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: GenericFacet

-- Begin accepted block: SubtypeDimension

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma direction_rank_subtype_image (W : Submodule ℝ E) (S : Set W) :
    Module.finrank ℝ (affineSpan ℝ (Subtype.val '' S : Set E)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have he : (Subtype.val '' S : Set E) = W.subtype.toAffineMap '' S := rfl
  rw [he,← AffineSubspace.map_span,AffineSubspace.map_direction]
  exact Submodule.finrank_map_subtype_eq W _

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: SubtypeDimension

-- Begin accepted block: NativeFacet

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: NativeFacet

-- Begin accepted block: NativeInterior

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: NativeInterior

-- Begin accepted block: GenericFree

namespace MaxLatticeFree.Geometry.PolytopeProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Interior lattice-freeness in the space currently under consideration. -/
def Free (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Convex ℝ S ∧ ∀ x ∈ interior S, x ∉ Γ

/-- Maximality among convex sets free of the specified additive subgroup. -/
def MaxFree (Γ : AddSubgroup E) (S : Set E) : Prop :=
  Free Γ S ∧ ∀ K : Set E, Free Γ K → S ⊆ K → K = S

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: GenericFree

-- Begin accepted block: NativeFree

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: NativeFree

-- Begin accepted block: SubtypeFacet

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: SubtypeFacet

-- Begin accepted block: NativePolyhedron

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: NativePolyhedron

-- Begin accepted block: DiscreteFinite

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: DiscreteFinite

-- Begin accepted block: LatticeDiscrete

open Set Metric
namespace MaxLatticeFree.Geometry.PolytopeProof
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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: LatticeDiscrete

-- Begin accepted block: SupportingFunctional

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: SupportingFunctional

-- Begin accepted block: BoundedPolyhedral

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: BoundedPolyhedral

-- Begin accepted block: PolyRecession

open Set

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: PolyRecession

-- Begin accepted block: FacetLatticePoint

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof
-- End accepted block: FacetLatticePoint

namespace MaxLatticeFree.Geometry.PolytopeProof

lemma native_lattice_comap_discrete {n : ℕ} {Γ : AddSubgroup (EuclideanSpace ℝ (Fin n))}
    {V : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (h : IsLatticeOf Γ V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Γ.comap V.subtype.toAddMonoidHom, ‖g‖ < ε → g = 0 := by
  obtain ⟨ε,hε,hg⟩ := native_lattice_discrete h
  exact ⟨ε,hε,fun g hm hn => Subtype.ext (hg g hm hn)⟩


end MaxLatticeFree.Geometry.PolytopeProof

namespace MaxLatticeFree.Geometry.PolytopeProof

variable {n : ℕ}

lemma nativeFacet_subtype_iff (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S F : Set (EuclideanSpace ℝ (Fin n))) (hS : S⊆(W : Set _)) (hF : F⊆(W : Set _)) :
    IsFacet S F ↔ GFacet ((Subtype.val : W → _) ⁻¹' S) ((Subtype.val : W → _) ⁻¹' F) := by
  rw [nativeFacet_iff_gFacet,← subtype_image_preimage_of_subset W S hS,
    ← subtype_image_preimage_of_subset W F hF,gFacet_subtype_image_iff]
  simp only [Set.preimage_image_eq _ Subtype.val_injective]


end MaxLatticeFree.Geometry.PolytopeProof

/- Complete proof bodies from FiniteHull.lean. -/

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.PolytopeProof

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

end MaxLatticeFree.Geometry.PolytopeProof

/- Complete proof bodies from FacetInterior.lean. -/

open Set Filter
open scoped Topology

namespace MaxLatticeFree.Geometry.PolytopeProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma strict_row_mem_intrinsicInterior (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι)
    {z : E} (hz : a i z = b i) (hstrict : ∀ j, j ≠ i → a j z < b j) :
    z ∈ intrinsicInterior ℝ (rowFace a b i) := by
  have hzP : z ∈ polyBody a b := by
    intro j
    by_cases hj : j = i
    · simpa [hj] using hz.le
    · exact (hstrict j hj).le
  have hzF : z ∈ rowFace a b i := ⟨hzP, hz⟩
  let zz : affineSpan ℝ (rowFace a b i) := ⟨z, subset_affineSpan ℝ _ hzF⟩
  have hlevel : ∀ y ∈ affineSpan ℝ (rowFace a b i), a i y = b i := by
    intro y hy
    rw [rowFace_affineSpan a b i hz hstrict] at hy
    change a i (y - z) = 0 at hy
    rw [map_sub, hz] at hy
    exact sub_eq_zero.mp hy
  have hevent : ∀ j, ∀ᶠ y : affineSpan ℝ (rowFace a b i) in 𝓝 zz,
      j ≠ i → a j y < b j := by
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall (fun _ h => (h hj).elim)
    · have hc : Continuous (fun y : affineSpan ℝ (rowFace a b i) => a j y) :=
        (a j).continuous_of_finiteDimensional.comp continuous_subtype_val
      filter_upwards [(hc.tendsto zz).eventually (gt_mem_nhds (hstrict j hj))] with y hy
      exact fun _ => hy
  refine ⟨zz, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  filter_upwards [eventually_all.mpr hevent] with y hy
  refine ⟨?_, hlevel y y.property⟩
  intro j
  by_cases hj : j = i
  · simpa [hj] using (hlevel y y.property).le
  · exact (hy j hj).le

end MaxLatticeFree.Geometry.PolytopeProof


open Set MaxLatticeFree.Geometry MaxLatticeFree.Geometry.PolytopeProof

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S) (hbdd : Bornology.IsBounded S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) :
    IsPolytope S ∧ ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → ∃ x ∈ Λ, x ∈ relint F := by
  classical
  let P : Set V := Subtype.val ⁻¹' S
  let Γ := Λ.comap V.subtype.toAddMonoidHom
  have hp : MaxFree Γ P := (nativeMaxFree_iff Λ V S hS.1.1).mp hS
  have hi : (interior P).Nonempty := (nativeFullDim_iff V S hS.1.1 hS.1.2.1).mp hdim
  have hb : Bornology.IsBounded P := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
    exact isBounded_iff_forall_norm_le.mpr ⟨R, fun x hx => hR x hx⟩
  have hΓ := native_lattice_comap_discrete hΛ
  obtain ⟨t, a, b, he, hw⟩ := polyhedral_irredundant (bounded_maxFree_polyhedral Γ hΓ hp hi hb)
  have hiB : (interior (polyBody a b)).Nonempty := he ▸ hi
  have hbB : Bornology.IsBounded (polyBody a b) := he ▸ hb
  have hpB : MaxFree Γ (polyBody a b) := he ▸ hp
  have hSP : Subtype.val '' P = S := subtype_image_preimage_of_subset V S hS.1.1
  constructor
  · obtain ⟨A, hA⟩ := bounded_polyBody_finite_hull a b hbB
    refine ⟨A.image Subtype.val, ?_⟩
    rw [← hSP, he, hA, Finset.coe_image]
    exact LinearMap.image_convexHull V.subtype _
  · intro F hF
    have hFS : F ⊆ S := ((nativeFacet_iff_gFacet S F).mp hF).subset
    have hFW : F ⊆ (V : Set _) := hFS.trans hS.1.1
    have hFG : GFacet P ((Subtype.val : V → _) ⁻¹' F) :=
      (nativeFacet_subtype_iff V S F hS.1.1 hFW).mp hF
    rw [he] at hFG
    obtain ⟨i, hiF⟩ := gFacet_eq_rowFace a b hiB hw hFG
    obtain ⟨z, hz, hzi, hzo⟩ := bounded_irredundant_lattice_point Γ hΓ a b hpB hiB hbB hw i
    refine ⟨(z : EuclideanSpace ℝ (Fin n)), hz, ?_⟩
    have hFimage : (Subtype.val : V → _) '' rowFace a b i = F := by
      rw [← hiF]
      exact subtype_image_preimage_of_subset V F hFW
    rw [relint_eq_intrinsicInterior, ← hFimage]
    have himg := V.subtypeₗᵢ.toAffineIsometry.intrinsicInterior_image (rowFace a b i)
    simp only [LinearIsometry.coe_toAffineIsometry, Submodule.coe_subtypeₗᵢ] at himg
    have hmem : V.subtype z ∈ V.subtype '' intrinsicInterior ℝ (rowFace a b i) :=
      mem_image_of_mem _ (strict_row_mem_intrinsicInterior a b i hzi hzo)
    rw [← himg] at hmem
    exact hmem
