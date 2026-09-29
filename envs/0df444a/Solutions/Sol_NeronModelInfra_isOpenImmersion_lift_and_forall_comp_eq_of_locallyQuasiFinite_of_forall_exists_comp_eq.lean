-- Prove2me | solution 1 for NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5aa1097e-3d9c-5a8e-bfaa-64745abe9204

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mLaw535S

section Topology

theorem dense_of_forall_dense_fibre {X Z : Type*} [TopologicalSpace X] (p : X → Z) (S : Set X)
    (h : ∀ z : Z, Dense ((Subtype.val : {x : X // p x = z} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈
      closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) := h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

theorem dense_of_forall_maximal_mem {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    [NoetherianSpace X] {W : Set X} (hW : ∀ x : X, (∀ x' : X, x' ⤳ x → x' = x) → x ∈ W) :
    Dense W := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨o, ho⟩
  set C := irreducibleComponent o with hC
  have hCmem : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents o
  obtain ⟨η, hη⟩ := QuasiSober.sober hCmem.1 (isClosed_of_mem_irreducibleComponents C hCmem)
  have hηo : η ⤳ o := by
    rw [specializes_iff_mem_closure, hη.def]
    exact mem_irreducibleComponent
  have hηmax : ∀ x' : X, x' ⤳ η → x' = η := by
    intro x' hx'
    have h1 : C ⊆ closure {x'} := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hx')) isClosed_closure
    have h2 : closure {x'} ⊆ C := hCmem.2 isIrreducible_singleton.closure h1
    have hx'gen : IsGenericPoint x' C := h2.antisymm h1
    exact hx'gen.eq hη
  exact ⟨η, hηo.mem_open hO ho, hW η hηmax⟩

theorem dense_image_of_denseRange {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Z}
    (hf : Continuous f) (hr : DenseRange f) {S : Set X} (hS : Dense S) : Dense (f '' S) :=
  hr.dense_image hf hS

end Topology

section Charts

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (i₁ i₂ : SchemeHomOver y y')

def ch : pullback y y ⟶ pullback y' y' :=
  pullback.map y y y' y' i₁.1 i₂.1 (𝟙 _) (by rw [Category.comp_id, i₁.2]) (by rw [Category.comp_id, i₂.2])

@[reassoc (attr := simp)]
theorem ch_fst : ch y y' i₁ i₂ ≫ pullback.fst y' y' = pullback.fst y y ≫ i₁.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ch_snd : ch y y' i₁ i₂ ≫ pullback.snd y' y' = pullback.snd y y ≫ i₂.1 := pullback.lift_snd _ _ _

scoped instance isOpenImmersion_ch [IsOpenImmersion i₁.1] [IsOpenImmersion i₂.1] :
    IsOpenImmersion (ch y y' i₁ i₂) := by
  unfold ch; infer_instance

theorem range_ch [IsOpenImmersion i₁.1] [IsOpenImmersion i₂.1] :
    Set.range (ch y y' i₁ i₂) =
      (pullback.fst y' y') ⁻¹' Set.range i₁.1 ∩ (pullback.snd y' y') ⁻¹' Set.range i₂.1 := by
  unfold ch; exact Scheme.Pullback.range_map y y y' y' i₁.1 i₂.1 (𝟙 _) _ _

theorem dense_range_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) :
    Dense (Set.range (ch y y' ι ι)) := by

  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian y'
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace y'
  haveI : IsNoetherian Y' := {}
  have hd : Dense (Set.range ι.1.base) :=
    dense_of_forall_maximal_mem fun p hp => hιd p fun p' h _ => hp p' h
  rw [range_ch]
  exact (hd.preimage (pullback.fst y' y').isOpenMap).inter_of_isOpen_left
    (hd.preimage (pullback.snd y' y').isOpenMap) ((pullback.fst y' y').continuous.isOpen_preimage _ ι.1.isOpenEmbedding.isOpen_range)

theorem dense_image_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    {S : Set ↑(pullback y y)} (hS : Dense S) : Dense ((ch y y' ι ι) '' S) := by
  have h1 : Set.range (ch y y' ι ι) ⊆ closure ((ch y y' ι ι) '' S) := by
    rw [← Set.image_univ, ← hS.closure_eq]
    exact image_closure_subset_closure_image (ch y y' ι ι).continuous
  intro z
  have := (dense_range_ch y y' ι hιd).closure_eq
  have h2 : closure (Set.range (ch y y' ι ι)) ⊆ closure ((ch y y' ι ι) '' S) :=
    closure_minimal h1 isClosed_closure
  exact h2 (this ▸ Set.mem_univ z)

end Charts

section Assoc

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

abbrev DD : Scheme.{u} := pullback (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

abbrev Q12 : DD y D ⟶ D := pullback.fst (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

abbrev Q23 : DD y D ⟶ D := pullback.snd (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

@[reassoc]
theorem Q12_snd : Q12 y D ≫ D.ι ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem fst_y : pullback.fst y y ≫ y = pullback.snd y y ≫ y :=
  pullback.condition

@[reassoc]
theorem M_y : M.1 ≫ y = D.ι ≫ pullback.fst y y ≫ y := M.2

def mulFst : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ M.1) (Q23 y D ≫ D.ι ≫ pullback.snd y y)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

def mulSnd : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ D.ι ≫ pullback.fst y y) (Q23 y D ≫ M.1)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

@[reassoc (attr := simp)]
theorem mulFst_fst : mulFst y D M ≫ pullback.fst y y = Q12 y D ≫ M.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulFst_snd : mulFst y D M ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.snd y y :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_fst : mulSnd y D M ≫ pullback.fst y y = Q12 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_snd : mulSnd y D M ≫ pullback.snd y y = Q23 y D ≫ M.1 := pullback.lift_snd _ _ _

abbrev A0 : Scheme.{u} := pullback (D.ι ≫ pullback.snd y y) (pullback.fst y y)

abbrev B0 : Scheme.{u} := pullback M.1 (pullback.fst y y)

@[reassoc]
theorem A0_cond : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y =
    pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem B0_cond : pullback.fst M.1 (pullback.fst y y) ≫ M.1 =
    pullback.snd M.1 (pullback.fst y y) ≫ pullback.fst y y :=
  pullback.condition

theorem A0_cond_y : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ M.1 ≫ y =
    pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.snd y y ≫ y := by
  have h : pullback.fst (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y ≫ y =
      pullback.snd (D.ι ≫ pullback.snd y y) (pullback.fst y y) ≫ pullback.fst y y ≫ y := by
    rw [A0_cond_assoc]
  simp only [M_y, fst_y] at h ⊢
  exact h

theorem B0_cond_y : pullback.fst M.1 (pullback.fst y y) ≫ D.ι ≫ pullback.snd y y ≫ y =
    pullback.snd M.1 (pullback.fst y y) ≫ pullback.snd y y ≫ y := by
  have h : pullback.fst M.1 (pullback.fst y y) ≫ M.1 ≫ y =
      pullback.snd M.1 (pullback.fst y y) ≫ pullback.fst y y ≫ y := by
    rw [B0_cond_assoc]
  simp only [M_y, fst_y] at h ⊢
  exact h

abbrev i0 : DD y D ⟶ A0 y D :=
  pullback.map _ _ _ _ (𝟙 _) D.ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])

def kA : A0 y D ⟶ B0 y D M :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ M.1) (pullback.snd _ _ ≫ pullback.snd y y)
      (by simp only [Category.assoc]; exact A0_cond_y y D M))
    (by rw [pullback.lift_fst])

def kB : B0 y D M ⟶ A0 y D :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ D.ι ≫ pullback.snd y y)
      (pullback.snd _ _ ≫ pullback.snd y y)
      (by simp only [Category.assoc]; exact B0_cond_y y D M))
    (by rw [pullback.lift_fst])

theorem kA_kB : kA y D M ≫ kB y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [kA, kB, Category.assoc, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [kA, kB, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp, A0_cond]
    · simp only [kA, kB, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]

theorem kB_kA : kB y D M ≫ kA y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [kA, kB, Category.assoc, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [kA, kB, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp, B0_cond]
    · simp only [kA, kB, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]

scoped instance : IsIso (kA y D M) := ⟨kB y D M, kA_kB y D M, kB_kA y D M⟩

theorem mulFst_eq : mulFst y D M = i0 y D ≫ kA y D M ≫ pullback.snd M.1 (pullback.fst y y) := by
  apply pullback.hom_ext
  · rw [mulFst_fst, Category.assoc, Category.assoc, ← B0_cond]
    simp only [kA, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [mulFst_snd, Category.assoc, kA, pullback.lift_snd_assoc, pullback.lift_snd]

theorem universallyOpen_mulFst [UniversallyOpen M.1] : UniversallyOpen (mulFst y D M) := by
  rw [mulFst_eq]
  infer_instance

abbrev A0' : Scheme.{u} := pullback (pullback.snd y y) (D.ι ≫ pullback.fst y y)

abbrev B0' : Scheme.{u} := pullback (pullback.snd y y) M.1

@[reassoc]
theorem A0'_cond : pullback.fst (pullback.snd y y) (D.ι ≫ pullback.fst y y) ≫ pullback.snd y y =
    pullback.snd (pullback.snd y y) (D.ι ≫ pullback.fst y y) ≫ D.ι ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem B0'_cond : pullback.fst (pullback.snd y y) M.1 ≫ pullback.snd y y =
    pullback.snd (pullback.snd y y) M.1 ≫ M.1 :=
  pullback.condition

abbrev i0' : DD y D ⟶ A0' y D :=
  pullback.map _ _ _ _ D.ι (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

def kA' : A0' y D ⟶ B0' y D M :=
  pullback.lift
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ pullback.fst y y) (pullback.snd _ _ ≫ M.1)
      (by simp only [Category.assoc, M_y, fst_y, A0'_cond_assoc]))
    (pullback.snd _ _)
    (by rw [pullback.lift_snd])

def kB' : B0' y D M ⟶ A0' y D :=
  pullback.lift
    (pullback.lift (f := y) (g := y) (pullback.fst _ _ ≫ pullback.fst y y)
      (pullback.snd _ _ ≫ D.ι ≫ pullback.fst y y)
      (by simp only [Category.assoc, M_y, fst_y, B0'_cond_assoc]))
    (pullback.snd _ _)
    (by rw [pullback.lift_snd])

theorem kA'_kB' : kA' y D M ≫ kB' y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, A0'_cond]
  · simp only [kA', kB', Category.assoc, pullback.lift_snd, Category.id_comp]

theorem kB'_kA' : kB' y D M ≫ kA' y D M = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · simp only [kA', kB', Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, B0'_cond]
  · simp only [kA', kB', Category.assoc, pullback.lift_snd, Category.id_comp]

scoped instance : IsIso (kA' y D M) := ⟨kB' y D M, kA'_kB' y D M, kB'_kA' y D M⟩

theorem mulSnd_eq : mulSnd y D M = i0' y D ≫ kA' y D M ≫ pullback.fst (pullback.snd y y) M.1 := by
  apply pullback.hom_ext
  · simp only [mulSnd_fst, Category.assoc, kA', pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [mulSnd_snd, Category.assoc, Category.assoc, B0'_cond]
    simp only [kA', pullback.lift_snd_assoc, Category.comp_id]

theorem universallyOpen_mulSnd [UniversallyOpen M.1] : UniversallyOpen (mulSnd y D M) := by
  rw [mulSnd_eq]
  infer_instance

def A : (DD y D).Opens := mulFst y D M ⁻¹ᵁ D ⊓ mulSnd y D M ⁻¹ᵁ D

theorem mem_A (x : ↑(DD y D)) : x ∈ A y D M ↔ (mulFst y D M).base x ∈ D ∧ (mulSnd y D M).base x ∈ D := by
  simp only [A, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage]

theorem range_A_mulFst : Set.range ((A y D M).ι ≫ mulFst y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact ((mem_A y D M x.1).mp x.2).1

theorem range_A_mulSnd : Set.range ((A y D M).ι ≫ mulSnd y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact ((mem_A y D M x.1).mp x.2).2

def dF : (A y D M : Scheme.{u}) ⟶ D := IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulFst y D M) (range_A_mulFst y D M)

def dG : (A y D M : Scheme.{u}) ⟶ D := IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulSnd y D M) (range_A_mulSnd y D M)

@[reassoc (attr := simp)]
theorem dF_ι : dF y D M ≫ D.ι = (A y D M).ι ≫ mulFst y D M := IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem dG_ι : dG y D M ≫ D.ι = (A y D M).ι ≫ mulSnd y D M := IsOpenImmersion.lift_fac _ _ _

def FF : (A y D M : Scheme.{u}) ⟶ Y := dF y D M ≫ M.1

def GG : (A y D M : Scheme.{u}) ⟶ Y := dG y D M ≫ M.1

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable (hUD : U ≤ D) (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1)

include hM in

theorem comp_m_eq {T : Scheme.{u}} (w : T ⟶ U) (d : T ⟶ D) (h : w ≫ U.ι = d ≫ D.ι) : w ≫ m.1 = d ≫ M.1 := by
  rw [← hM, ← Category.assoc]
  congr 1
  rw [← cancel_mono D.ι, Category.assoc, Scheme.homOfLE_ι, h]

def L : (A y D M : Scheme.{u}).Opens :=
  ((A y D M).ι ≫ Q12 y D ≫ D.ι) ⁻¹ᵁ U ⊓ ((A y D M).ι ≫ Q23 y D ≫ D.ι) ⁻¹ᵁ U ⊓
    ((A y D M).ι ≫ mulFst y D M) ⁻¹ᵁ U ⊓ ((A y D M).ι ≫ mulSnd y D M) ⁻¹ᵁ U

theorem mem_L (x : ↑(A y D M)) :
    x ∈ L y D M U ↔
      D.ι.base ((Q12 y D).base (((A y D M).ι).base x)) ∈ U ∧
      D.ι.base ((Q23 y D).base (((A y D M).ι).base x)) ∈ U ∧
      (mulFst y D M).base (((A y D M).ι).base x) ∈ U ∧ (mulSnd y D M).base (((A y D M).ι).base x) ∈ U := by
  simp only [L, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, and_assoc]

theorem dense_L [Smooth y] [UniversallyOpen M.1] (hU : Dense (U : Set ↑(pullback y y))) :
    Dense (L y D M U : Set ↑(A y D M)) := by
  haveI := universallyOpen_mulFst y D M
  haveI := universallyOpen_mulSnd y D M
  have h1 : Dense (((A y D M).ι ≫ Q12 y D ≫ D.ι) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h2 : Dense (((A y D M).ι ≫ Q23 y D ≫ D.ι) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h3 : Dense (((A y D M).ι ≫ mulFst y D M) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  have h4 : Dense (((A y D M).ι ≫ mulSnd y D M) ⁻¹ᵁ U : Set ↑(A y D M)) :=
    hU.preimage (Scheme.Hom.isOpenMap _)
  simp only [L, TopologicalSpace.Opens.coe_inf]
  exact ((h1.inter_of_isOpen_left h2 (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h3
    (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_right h4 (TopologicalSpace.Opens.isOpen _)

variable (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)

include hM hassoc in

theorem FF_eq_GG [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y] [UniversallyOpen M.1]
    (hU : Dense (U : Set ↑(pullback y y))) : FF y D M = GG y D M := by

  haveI : IsReduced (A y D M : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      ((A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y)
  haveI : IsDominant (L y D M U).ι := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact dense_L y D M U hU
  refine ext_of_isDominant_of_isSeparated y ?_ (L y D M U).ι ?_
  · simp only [FF, GG, Category.assoc, M_y, dF_ι_assoc, dG_ι_assoc, mulFst_fst_assoc, mulSnd_fst_assoc]
  have memL := fun x : ↑(L y D M U) => (mem_L y D M U x.1).mp x.2
  have hrU : Set.range U.ι.base = (U : Set ↑(pullback y y)) := Scheme.Opens.range_ι U

  have hr₁ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D ≫ D.ι).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have := (memL x).1
    rwa [Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at this
  have hr₂ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ Q23 y D ≫ D.ι).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have := (memL x).2.1
    rwa [Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at this
  have hr₃ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ mulFst y D M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have := (memL x).2.2.1
    rwa [Scheme.Opens.ι_apply] at this
  have hr₄ : Set.range ((L y D M U).ι ≫ (A y D M).ι ≫ mulSnd y D M).base ⊆ Set.range U.ι.base := by
    rw [hrU]; rintro _ ⟨x, rfl⟩
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have := (memL x).2.2.2
    rwa [Scheme.Opens.ι_apply] at this
  let t : (L y D M U : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
    (L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y
  have e₁ := IsOpenImmersion.lift_fac U.ι _ hr₁
  have e₂ := IsOpenImmersion.lift_fac U.ι _ hr₂
  have e₃ := IsOpenImmersion.lift_fac U.ι _ hr₃
  have e₄ := IsOpenImmersion.lift_fac U.ι _ hr₄
  let uu : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₁, by rw [reassoc_of% e₁]⟩
  let vv : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₂, by rw [reassoc_of% e₂, ← Q12_snd_assoc, ← fst_y]⟩
  let pp : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₃, by rw [reassoc_of% e₃, mulFst_fst_assoc, M_y]⟩
  let qq : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨IsOpenImmersion.lift U.ι _ hr₄, by rw [reassoc_of% e₄, mulSnd_fst_assoc]⟩

  have m₁ : uu.1 ≫ m.1 = ((L y D M U).ι ≫ (A y D M).ι ≫ Q12 y D) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₁, Category.assoc, Category.assoc])
  have m₂ : vv.1 ≫ m.1 = ((L y D M U).ι ≫ (A y D M).ι ≫ Q23 y D) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₂, Category.assoc, Category.assoc])
  have m₃ : pp.1 ≫ m.1 = ((L y D M U).ι ≫ dF y D M) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₃, Category.assoc, dF_ι])
  have m₄ : qq.1 ≫ m.1 = ((L y D M U).ι ≫ dG y D M) ≫ M.1 :=
    comp_m_eq y D M U m hUD hM _ _ (by rw [e₄, Category.assoc, dG_ι])
  have key := hassoc t uu vv pp qq
    (by rw [reassoc_of% e₁, reassoc_of% e₂, Q12_snd])
    (by rw [m₁, reassoc_of% e₃, mulFst_fst, Category.assoc, Category.assoc])
    (by rw [reassoc_of% e₃, reassoc_of% e₂, mulFst_snd])
    (by rw [reassoc_of% e₄, reassoc_of% e₁, mulSnd_fst])
    (by rw [m₂, reassoc_of% e₄, mulSnd_snd, Category.assoc, Category.assoc])
  rw [m₃, m₄] at key
  simpa only [FF, GG, Category.assoc] using key

include hM hassoc in

theorem assoc_ext [IsDomain R] [IsDiscreteValuationRing R] [Smooth y] [IsSeparated y] [UniversallyOpen M.1]
    (hU : Dense (U : Set ↑(pullback y y)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y))
    (h₁ : u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y)
    (h₂ : p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1)
    (h₃ : p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y)
    (h₄ : q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y)
    (h₅ : q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1) :
    p.1 ≫ M.1 = q.1 ≫ M.1 := by

  let τ₀ : T ⟶ DD y D := pullback.lift u.1 v.1 h₁
  have hF : τ₀ ≫ mulFst y D M = p.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulFst_fst, pullback.lift_fst_assoc, Category.assoc, h₂]
    · rw [Category.assoc, mulFst_snd, pullback.lift_snd_assoc, Category.assoc, h₃]
  have hG : τ₀ ≫ mulSnd y D M = q.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulSnd_fst, pullback.lift_fst_assoc, Category.assoc, h₄]
    · rw [Category.assoc, mulSnd_snd, pullback.lift_snd_assoc, Category.assoc, h₅]
  have hr : Set.range τ₀.base ⊆ Set.range (A y D M).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine (mem_A y D M _).mpr ⟨?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hF, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (p.1.base x).2
    · rw [← Scheme.Hom.comp_apply, hG, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (q.1.base x).2
  let τ : T ⟶ A y D M := IsOpenImmersion.lift (A y D M).ι τ₀ hr
  have hτ : τ ≫ (A y D M).ι = τ₀ := IsOpenImmersion.lift_fac _ _ _
  have hp : p.1 = τ ≫ dF y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dF_ι, reassoc_of% hτ, hF]
  have hq : q.1 = τ ≫ dG y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dG_ι, reassoc_of% hτ, hG]
  have key := congrArg (fun φ => τ ≫ φ) (FF_eq_GG y D M U m hUD hM hassoc hU)
  simp only [FF, GG] at key
  rw [hp, hq, Category.assoc, Category.assoc]
  exact key

end Assoc

section ZMT

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y']
  (U' : (pullback y' y').Opens)

theorem isOpenImmersion_of_zmt (f : (U' : Scheme.{u}) ⟶ pullback y' y') [LocallyQuasiFinite f]
    (pr : pullback y' y' ⟶ Y') [IsSeparated pr] [LocallyOfFiniteType pr] (hf : f ≫ pr = U'.ι ≫ pr)
    (V : (pullback y' y').Opens) (hV : Dense (V : Set ↑(pullback y' y')))
    (s : (V : Scheme.{u}) ⟶ U') (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) : IsOpenImmersion f := by
  haveI : IsLocallyNoetherian (pullback y' y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y' y' ≫ y')
  haveI : CompactSpace ↑(pullback y' y') :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst y' y' ≫ y')
  haveI : IsNoetherian (pullback y' y') := {}
  haveI : NoetherianSpace ↑(U' : Scheme.{u}) := U'.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : IsReduced (U' : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (U'.ι ≫ pullback.fst y' y' ≫ y')
  haveI : IsSeparated (f ≫ pr) := by rw [hf]; infer_instance
  haveI : IsSeparated f := IsSeparated.of_comp f pr
  haveI : LocallyOfFiniteType (f ≫ pr) := by rw [hf]; infer_instance
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pr
  haveI : QuasiCompact f := inferInstance
  have hY : ∀ z : ↑(pullback y' y'), IsDomain ((pullback y' y').presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback y' y').presheaf.stalk z) := fun z =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst y' y' ≫ y') z
  exact AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    f hY V hV s hs hsd

end ZMT

section Ext

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
  (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

def U0 : (pullback y' y').Opens := ch y y' ι ι ''ᵁ U

def e0 : (U : Scheme.{u}) ≅ (U0 y U y' ι : Scheme.{u}) := (ch y y' ι ι).isoImage U

@[reassoc] theorem e0_hom_ι : (e0 y U y' ι).hom ≫ (U0 y U y' ι).ι = U.ι ≫ ch y y' ι ι :=
  Scheme.Hom.isoImage_hom_ι _ _

@[reassoc] theorem e0_inv_ι : (e0 y U y' ι).inv ≫ U.ι ≫ ch y y' ι ι = (U0 y U y' ι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _

def m0 : SchemeHomOver ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y') y' :=
  ⟨(e0 y U y' ι).inv ≫ m.1 ≫ ι.1, by
    rw [Category.assoc, Category.assoc, ι.2, m.2, ← e0_inv_ι_assoc, ch_fst_assoc, ι.2]⟩

theorem m0_val : (m0 y U m y' ι).1 = (e0 y U y' ι).inv ≫ m.1 ≫ ι.1 := rfl

variable (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
  ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
    w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
    w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
    w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)

omit [IsOpenImmersion ι.1] in
include hext in

theorem exists_w0 : ∃ w₀ : (U : Scheme.{u}) ⟶ U', w₀ ≫ U'.ι = U.ι ≫ ch y y' ι ι ∧ w₀ ≫ m'.1 = m.1 ≫ ι.1 := by
  obtain ⟨w', h1, h2, h3⟩ := hext (U.ι ≫ pullback.fst y y ≫ y) ⟨𝟙 _, Category.id_comp _⟩
  refine ⟨w'.1, ?_, by rw [h3, Category.id_comp]⟩
  apply pullback.hom_ext
  · rw [Category.assoc, h1, Category.id_comp, Category.assoc, ch_fst]
  · rw [Category.assoc, h2, Category.id_comp, Category.assoc, ch_snd]

variable {y U m y' ι U' m'}

section W0

variable (w₀ : (U : Scheme.{u}) ⟶ U') (hw₀ : w₀ ≫ U'.ι = U.ι ≫ ch y y' ι ι) (hw₀m : w₀ ≫ m'.1 = m.1 ≫ ι.1)

include hw₀ in
theorem U0_le : U0 y U y' ι ≤ U' := by
  intro z hz
  have hz' : z ∈ ((U0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := hz
  rw [U0, Scheme.Hom.coe_image] at hz'
  obtain ⟨u, hu, rfl⟩ := hz'
  have : (ch y y' ι ι).base u = U'.ι.base (w₀.base ⟨u, hu⟩) := by
    rw [← Scheme.Hom.comp_apply, hw₀, Scheme.Hom.comp_apply]; rfl
  rw [this]; exact (w₀.base _).2

include hw₀ in
theorem e0_hom_homOfLE (h : U0 y U y' ι ≤ U') : (e0 y U y' ι).hom ≫ (pullback y' y').homOfLE h = w₀ := by
  rw [← cancel_mono U'.ι, Category.assoc, Scheme.homOfLE_ι, e0_hom_ι, hw₀]

include hw₀ hw₀m in
theorem homOfLE_m' (h : U0 y U y' ι ≤ U') : (pullback y' y').homOfLE h ≫ m'.1 = (m0 y U m y' ι).1 := by
  rw [m0_val, ← hw₀m, ← e0_hom_homOfLE w₀ hw₀ h, Category.assoc, Iso.inv_hom_id_assoc]

omit [IsOpenImmersion ι.1] in
include hw₀ hw₀m in

theorem w0_Phi' :
    w₀ ≫ pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm) = Phi y U m ≫ ch y y' ι ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, reassoc_of% hw₀, ch_fst, Category.assoc, ch_fst,
      pullback.lift_fst_assoc, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, hw₀m, Category.assoc, ch_snd, pullback.lift_snd_assoc]

omit [IsOpenImmersion ι.1] in
include hw₀ hw₀m in

theorem w0_Psi' :
    w₀ ≫ pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])) = Psi y U m ≫ ch y y' ι ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hw₀m, Category.assoc, ch_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, reassoc_of% hw₀, ch_snd, Category.assoc, ch_snd,
      pullback.lift_snd_assoc, Category.assoc]

include hw₀ in
theorem isOpenImmersion_w0 : IsOpenImmersion w₀ := by
  have : IsOpenImmersion (w₀ ≫ U'.ι) := by rw [hw₀]; infer_instance
  exact IsOpenImmersion.of_comp w₀ U'.ι

omit [IsOpenImmersion ι.1] in
include hw₀ in

theorem denseRange_w0 (hd : Dense ((ch y y' ι ι) '' (U : Set ↑(pullback y y)))) : DenseRange w₀.base := by
  have h1 : Set.range w₀.base = U'.ι.base ⁻¹' ((ch y y' ι ι) '' (U : Set ↑(pullback y y))) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨U.ι.base u, u.2, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hw₀, Scheme.Hom.comp_apply]
    · rintro ⟨q, hq, hz⟩
      refine ⟨⟨q, hq⟩, U'.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hw₀, Scheme.Hom.comp_apply]
      exact hz
  rw [DenseRange, h1]
  exact hd.preimage U'.ι.isOpenEmbedding.isOpenMap

theorem range_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  ext z; constructor
  · rintro ⟨x, rfl⟩; exact ⟨f.base x, ⟨x, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩

theorem exists_section (F : (U' : Scheme.{u}) ⟶ pullback y' y') (g : (U : Scheme.{u}) ⟶ pullback y' y')
    [IsOpenImmersion g] (hF : w₀ ≫ F = g) :
    ∃ s : (g.opensRange : Scheme.{u}) ⟶ U', s ≫ F = g.opensRange.ι ∧ Set.range s.base = Set.range w₀.base := by
  refine ⟨g.isoOpensRange.inv ≫ w₀, by rw [Category.assoc, hF, Scheme.Hom.isoOpensRange_inv_comp], ?_⟩
  ext z; constructor
  · rintro ⟨v, rfl⟩; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨g.isoOpensRange.hom.base u, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]⟩

end W0

variable (y U m y' ι) in

theorem hassoc_m0
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y'))
    (h₁ : u.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y')
    (h₂ : p.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y' = u.1 ≫ (m0 y U m y' ι).1)
    (h₃ : p.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y')
    (h₄ : q.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y' = u.1 ≫ (U0 y U y' ι).ι ≫ pullback.fst y' y')
    (h₅ : q.1 ≫ (U0 y U y' ι).ι ≫ pullback.snd y' y' = v.1 ≫ (m0 y U m y' ι).1) :
    p.1 ≫ (m0 y U m y' ι).1 = q.1 ≫ (m0 y U m y' ι).1 := by

  have cf : (U0 y U y' ι).ι ≫ pullback.fst y' y' = (e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y ≫ ι.1 := by
    rw [← e0_inv_ι_assoc, ch_fst]
  have cs : (U0 y U y' ι).ι ≫ pullback.snd y' y' = (e0 y U y' ι).inv ≫ U.ι ≫ pullback.snd y y ≫ ι.1 := by
    rw [← e0_inv_ι_assoc, ch_snd]
  have ht : ∀ r : SchemeHomOver t ((U0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y'),
      (r.1 ≫ (e0 y U y' ι).inv) ≫ U.ι ≫ pullback.fst y y ≫ y = t := by
    have hc : ((e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y) ≫ y =
        ((U0 y U y' ι).ι ≫ pullback.fst y' y') ≫ y' := by
      simp only [cf, Category.assoc, ι.2]
    intro r
    calc (r.1 ≫ (e0 y U y' ι).inv) ≫ U.ι ≫ pullback.fst y y ≫ y
        = r.1 ≫ (((e0 y U y' ι).inv ≫ U.ι ≫ pullback.fst y y) ≫ y) := by simp only [Category.assoc]
      _ = r.1 ≫ (((U0 y U y' ι).ι ≫ pullback.fst y' y') ≫ y') := by rw [hc]
      _ = t := by simpa only [Category.assoc] using r.2
  let u' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨u.1 ≫ (e0 y U y' ι).inv, ht u⟩
  let v' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨v.1 ≫ (e0 y U y' ι).inv, ht v⟩
  let p' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨p.1 ≫ (e0 y U y' ι).inv, ht p⟩
  let q' : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y) := ⟨q.1 ≫ (e0 y U y' ι).inv, ht q⟩
  simp only [m0_val, cf, cs] at h₁ h₂ h₃ h₄ h₅ ⊢
  simp only [← Category.assoc] at h₁ h₂ h₃ h₄ h₅ ⊢
  rw [cancel_mono] at h₁ h₂ h₃ h₄ h₅
  simp only [Category.assoc] at h₁ h₂ h₃ h₄ h₅
  have key := hassoc t u' v' p' q'
    (by simpa only [u', v', Category.assoc] using h₁) (by simpa only [u', p', Category.assoc] using h₂)
    (by simpa only [v', p', Category.assoc] using h₃) (by simpa only [u', q', Category.assoc] using h₄)
    (by simpa only [v', q', Category.assoc] using h₅)
  simp only [p', q', Category.assoc] at key
  simp only [Category.assoc]
  rw [reassoc_of% key]

end Ext

end P2mLaw535S
p2m_reactivate "P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq.P2mLaw535S"

open P2mLaw535S in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
        w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm))]
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])))] :
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
          ((Category.assoc _ _ _).trans m'.2.symm)) ∧
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
          (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
      p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
      q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1) := by
  haveI := hΦ
  haveI := hΨ

  obtain ⟨w₀, hw₀, hw₀m⟩ := exists_w0 y U m y' ι U' m' hext
  have hUD : U0 y U y' ι ≤ U' := U0_le w₀ hw₀
  have hM : (pullback y' y').homOfLE hUD ≫ m'.1 = (m0 y U m y' ι).1 := homOfLE_m' w₀ hw₀ hw₀m hUD

  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  have hΦU : Dense (Set.range (Phi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΦ₁
  have hΨU : Dense (Set.range (Psi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΨ₁
  have hU0 : Dense ((U0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := by
    rw [U0, Scheme.Hom.coe_image]; exact dense_image_ch y y' ι hιd hU
  have hdw₀ : DenseRange w₀.base := denseRange_w0 w₀ hw₀ (by rw [← Scheme.Hom.coe_image]; exact hU0)

  set Φ' := pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
    ((Category.assoc _ _ _).trans m'.2.symm) with hΦ'
  set Ψ' := pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
    (m'.2.trans (by rw [Category.assoc, pullback.condition])) with hΨ'
  have hΦ'oi : IsOpenImmersion Φ' := by
    obtain ⟨s, hs, hsr⟩ := exists_section w₀ Φ' (Phi y U m ≫ ch y y' ι ι) (w0_Phi' w₀ hw₀ hw₀m)
    refine isOpenImmersion_of_zmt y' U' Φ' (pullback.fst y' y') (pullback.lift_fst _ _ _) _ ?_ s hs ?_
    · rw [Scheme.Hom.coe_opensRange, range_comp]
      exact dense_image_ch y y' ι hιd hΦU
    · rw [DenseRange, hsr]; exact hdw₀
  have hΨ'oi : IsOpenImmersion Ψ' := by
    obtain ⟨s, hs, hsr⟩ := exists_section w₀ Ψ' (Psi y U m ≫ ch y y' ι ι) (w0_Psi' w₀ hw₀ hw₀m)
    refine isOpenImmersion_of_zmt y' U' Ψ' (pullback.snd y' y') (pullback.lift_snd _ _ _) _ ?_ s hs ?_
    · rw [Scheme.Hom.coe_opensRange, range_comp]
      exact dense_image_ch y y' ι hιd hΨU
    · rw [DenseRange, hsr]; exact hdw₀
  refine ⟨hΦ'oi, hΨ'oi, ?_⟩

  haveI : UniversallyOpen m'.1 := by
    have h : m'.1 = Φ' ≫ pullback.snd y' y' := (pullback.lift_snd _ _ _).symm
    rw [h]; infer_instance
  intro T t u v p q h₁ h₂ h₃ h₄ h₅
  exact assoc_ext y' U' m' (U0 y U y' ι) (m0 y U m y' ι) hUD hM
    (fun t u v p q => hassoc_m0 y U m y' ι hassoc t u v p q) hU0 t u v p q h₁ h₂ h₃ h₄ h₅

end
end S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
end P2MW
export P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq (solution)
