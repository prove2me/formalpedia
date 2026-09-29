-- Prove2me | solution 1 for NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/98e5642d-a334-55b1-9faf-9d1690b813ec

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mDomExt536

section General

theorem exists_lift_of_isClosedImmersion {D G Z : Scheme.{u}} [IsReduced D] (f : D ⟶ Z) (γ : G ⟶ Z)
    [IsClosedImmersion γ] (h : Set.range f.base ⊆ Set.range γ.base) : ∃ g : D ⟶ G, g ≫ γ = f := by
  haveI : Surjective (pullback.fst f γ) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro d
    exact h ⟨d, rfl⟩⟩
  haveI : IsIso (pullback.fst f γ) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f γ) ≫ pullback.snd f γ, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem dense_of_forall_dense_fibre {X Y : Type*} [TopologicalSpace X] (p : X → Y) (S : Set X)
    (h : ∀ y : Y, Dense ((Subtype.val : {x : X // p x = y} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈ closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) :=
    h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

theorem eq_univ_of_dense_subset {X : Type*} [TopologicalSpace X] {S C : Set X} (hS : Dense S)
    (hC : IsClosed C) (h : S ⊆ C) : C = Set.univ :=
  Set.eq_univ_of_univ_subset ((hS.closure_eq ▸ closure_minimal h hC :))

end General

section Graph

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable (D : (pullback y y).Opens) (hUD : U ≤ D) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)
variable (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1)

abbrev Y3g : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

abbrev grm : (U : Scheme.{u}) ⟶ Y3g y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

abbrev grM : (D : Scheme.{u}) ⟶ Y3g y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) D.ι M.1 M.2.symm

include hM in
theorem homOfLE_grM : (pullback y y).homOfLE hUD ≫ grM y D M = grm y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Scheme.homOfLE_ι]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hM]

theorem dense_range_homOfLE (hU : Dense (U : Set ↑(pullback y y))) :
    Dense (Set.range ((pullback y y).homOfLE hUD).base) := by
  have h1 : Set.range ((pullback y y).homOfLE hUD).base = D.ι.base ⁻¹' (U : Set ↑(pullback y y)) := by
    ext d
    constructor
    · rintro ⟨u, rfl⟩
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply]
      exact u.2
    · intro hd
      rw [Set.mem_preimage, Scheme.Opens.ι_apply] at hd
      refine ⟨⟨d.1, hd⟩, ?_⟩
      apply D.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
  rw [h1]
  exact hU.preimage D.ι.isOpenMap

include hM in

theorem range_grM_subset (hU : Dense (U : Set ↑(pullback y y))) :
    Set.range (grM y D M).base ⊆ closure (Set.range (grm y U m).base) := by
  have hC : (grM y D M).base ⁻¹' closure (Set.range (grm y U m).base) = Set.univ := by
    refine eq_univ_of_dense_subset (dense_range_homOfLE y U D hUD hU) (isClosed_closure.preimage
      (grM y D M).base.hom.continuous) ?_
    rintro _ ⟨u, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, homOfLE_grM y U m D hUD M hM]
    exact subset_closure ⟨u, rfl⟩
  rintro _ ⟨d, rfl⟩
  have : d ∈ (grM y D M).base ⁻¹' closure (Set.range (grm y U m).base) := by rw [hC]; trivial
  exact this

abbrev PhiM : (D : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1 ((Category.assoc _ _ _).trans M.2.symm)

abbrev PsiM : (D : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
    (M.2.trans (by rw [Category.assoc, pullback.condition]))

abbrev p13 : Y3g y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc]; exact pullback.condition)

abbrev p23 : Y3g y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

theorem grM_p13 : grM y D M ≫ p13 y = PhiM y D M := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd]

theorem grM_p23 : grM y D M ≫ p23 y ≫ (pullbackSymmetry y y).hom = PsiM y D M := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst, pullback.lift_snd]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc]

theorem exists_isOpenImmersion_comp_eq_grM [IsReduced (D : Scheme.{u})] {G : Scheme.{u}} (γ : G ⟶ Y3g y)
    [IsClosedImmersion γ] [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    (h : Set.range (grM y D M).base ⊆ Set.range γ.base) :
    ∃ g : (D : Scheme.{u}) ⟶ G, IsOpenImmersion g ∧ g ≫ γ = grM y D M := by
  obtain ⟨g, hg⟩ := exists_lift_of_isClosedImmersion (grM y D M) γ h
  have hgι : g ≫ (γ ≫ pullback.fst (pullback.fst y y ≫ y) y) = D.ι := by
    rw [← Category.assoc, hg, pullback.lift_fst]
  haveI : IsOpenImmersion (g ≫ (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)) := by
    rw [hgι]; infer_instance
  exact ⟨g, IsOpenImmersion.of_comp g (γ ≫ pullback.fst (pullback.fst y y ≫ y) y), hg⟩

theorem isOpenImmersion_PhiM_of {G : Scheme.{u}} (γ : G ⟶ Y3g y) (g : (D : Scheme.{u}) ⟶ G)
    [IsOpenImmersion g] (hg : g ≫ γ = grM y D M) [IsOpenImmersion (γ ≫ p13 y)] :
    IsOpenImmersion (PhiM y D M) := by
  have h : PhiM y D M = g ≫ (γ ≫ p13 y) := by rw [← grM_p13, ← hg, Category.assoc]
  rw [h]
  infer_instance

theorem isOpenImmersion_PsiM_of {G : Scheme.{u}} (γ : G ⟶ Y3g y) (g : (D : Scheme.{u}) ⟶ G)
    [IsOpenImmersion g] (hg : g ≫ γ = grM y D M) [IsOpenImmersion (γ ≫ p23 y)] :
    IsOpenImmersion (PsiM y D M) := by
  have h : PsiM y D M = g ≫ (γ ≫ p23 y) ≫ (pullbackSymmetry y y).hom := by
    rw [← grM_p23, ← hg]; simp only [Category.assoc]
  rw [h]
  infer_instance

theorem homOfLE_PhiM (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
    (pullback y y).homOfLE hUD ≫ PhiM y D M =
      pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Scheme.homOfLE_ι_assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hM]

theorem homOfLE_PsiM (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
    (pullback y y).homOfLE hUD ≫ PsiM y D M =
      pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition])) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hM]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Scheme.homOfLE_ι_assoc]

theorem dense_fibre_mono {X Z : Type*} [TopologicalSpace X] (p : X → Z) {S S' : Set X} (hSS' : S ⊆ S')
    (x : Z) (h : Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S') :=
  h.mono (Set.preimage_mono hSS')

theorem range_comp_subset {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base ⊆ Set.range g.base := by
  rintro _ ⟨a, rfl⟩
  exact ⟨f.base a, (Scheme.Hom.comp_apply f g a).symm⟩

end Graph

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

end P2mDomExt536
p2m_reactivate "P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre.P2mDomExt536"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (D : (pullback y y).Opens) (hUD : U ≤ D)
    (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)
    (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y →
        p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1 →
        p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y →
        q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y →
        q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1 →
        p.1 ≫ M.1 = q.1 ≫ M.1) := by

  obtain ⟨G, γ, hγ, -, hrange, hq12, hq13, hq23, -⟩ :=
    NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      y U m hU₁ hU₂ hΦ hΦ₁ hΦ₂ hΨ hΨ₁ hΨ₂ hassoc
  haveI := hγ
  haveI := hq12
  haveI := hq13
  haveI := hq23

  have hU : Dense (U : Set ↑(pullback y y)) :=
    P2mDomExt536.dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  haveI : IsReduced (D : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (D.ι ≫ pullback.fst y y ≫ y)

  have hsub : Set.range (P2mDomExt536.grM y D M).base ⊆ Set.range γ.base := by
    rw [hrange]
    exact P2mDomExt536.range_grM_subset y U m D hUD M hM hU
  obtain ⟨g, hg, hgγ⟩ := P2mDomExt536.exists_isOpenImmersion_comp_eq_grM y D M γ hsub
  haveI := hg
  have hΦM : IsOpenImmersion (P2mDomExt536.PhiM y D M) := P2mDomExt536.isOpenImmersion_PhiM_of y D M γ g hgγ
  have hΨM : IsOpenImmersion (P2mDomExt536.PsiM y D M) := P2mDomExt536.isOpenImmersion_PsiM_of y D M γ g hgγ
  haveI : UniversallyOpen M.1 := by
    have h : M.1 = P2mDomExt536.PhiM y D M ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
    rw [h]
    infer_instance

  have hUD' : (U : Set ↑(pullback y y)) ⊆ (D : Set ↑(pullback y y)) := hUD
  have hΦr : Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)).base ⊆ Set.range (P2mDomExt536.PhiM y D M).base := by
    rw [← P2mDomExt536.homOfLE_PhiM y U m D hUD M hM]
    exact P2mDomExt536.range_comp_subset _ _
  have hΨr : Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
      (m.2.trans (by rw [Category.assoc, pullback.condition]))).base ⊆
      Set.range (P2mDomExt536.PsiM y D M).base := by
    rw [← P2mDomExt536.homOfLE_PsiM y U m D hUD M hM]
    exact P2mDomExt536.range_comp_subset _ _
  refine ⟨fun x => P2mDomExt536.dense_fibre_mono _ hUD' x (hU₁ x),
    fun x => P2mDomExt536.dense_fibre_mono _ hUD' x (hU₂ x), hΦM,
    fun x => P2mDomExt536.dense_fibre_mono _ hΦr x (hΦ₁ x),
    fun x => P2mDomExt536.dense_fibre_mono _ hΦr x (hΦ₂ x), hΨM,
    fun x => P2mDomExt536.dense_fibre_mono _ hΨr x (hΨ₁ x),
    fun x => P2mDomExt536.dense_fibre_mono _ hΨr x (hΨ₂ x), ?_⟩
  intro T t u v p q h₁ h₂ h₃ h₄ h₅
  exact P2mDomExt536.assoc_ext y D M U m hUD hM hassoc hU t u v p q h₁ h₂ h₃ h₄ h₅

end
end S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
end P2MW
export P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre (solution)
