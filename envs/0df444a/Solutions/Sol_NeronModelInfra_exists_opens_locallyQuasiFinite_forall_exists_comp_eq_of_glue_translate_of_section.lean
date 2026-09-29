-- Prove2me | solution 1 for NeronModelInfra.exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4cd43ce8-2d25-5e9e-a13e-f995747e9112

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mLaw535G

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

theorem subset_closure_inter {X : Type*} [TopologicalSpace X] {O A A' : Set X} (hO : IsOpen O)
    (hA : IsOpen A) (h : O ⊆ closure A) (h' : O ⊆ closure A') : O ⊆ closure (A ∩ A') := by
  intro o ho
  rw [mem_closure_iff]
  intro N hN hoN
  obtain ⟨a₁, ⟨ha₁N, ha₁O⟩, ha₁A⟩ : (N ∩ O ∩ A).Nonempty :=
    mem_closure_iff.mp (h ho) (N ∩ O) (hN.inter hO) ⟨hoN, ho⟩
  obtain ⟨a₂, ⟨⟨ha₂N, -⟩, ha₂A⟩, ha₂A'⟩ : (N ∩ O ∩ A ∩ A').Nonempty :=
    mem_closure_iff.mp (h' ha₁O) (N ∩ O ∩ A) ((hN.inter hO).inter hA) ⟨⟨ha₁N, ha₁O⟩, ha₁A⟩
  exact ⟨a₂, ha₂N, ha₂A, ha₂A'⟩

theorem inter_image_subset_closure {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {c : X → Z}
    (hc : Continuous c) {P : Set Z} (hP : IsOpen P) {V V' : Set X} (h : V ⊆ closure V') :
    P ∩ c '' V ⊆ closure (P ∩ c '' V') := by
  refine subset_trans ?_ hP.inter_closure
  refine Set.inter_subset_inter_right _ ?_
  exact subset_trans (Set.image_mono h) (image_closure_subset_closure_image hc)

end General

section GlueDense

theorem denseRange_lift {X : Scheme.{u}} (Vi Vj W : X.Opens) (hWi : W ≤ Vi) (hWj : W ≤ Vj)
    (hcl : ((Vi ⊓ Vj : X.Opens) : Set X) ⊆ closure (W : Set X)) :
    DenseRange (pullback.lift (f := Vi.ι) (g := Vj.ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])).base := by
  set ℓ := pullback.lift (f := Vi.ι) (g := Vj.ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]) with hℓ
  have hℓι : ℓ ≫ pullback.fst Vi.ι Vj.ι ≫ Vi.ι = W.ι := by
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
  rw [DenseRange, dense_iff_inter_open]
  intro N hN ⟨n₀, hn₀⟩
  let e : ↑(pullback Vi.ι Vj.ι) → X := (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base
  have he : IsOpenEmbedding e := (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).isOpenEmbedding
  have hmem : ∀ n : ↑(pullback Vi.ι Vj.ι), e n ∈ ((Vi ⊓ Vj : X.Opens) : Set X) := by
    intro n
    refine ⟨?_, ?_⟩
    · change (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base n ∈ (Vi : Set X)
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ((pullback.fst Vi.ι Vj.ι).base n).2
    · change (pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base n ∈ (Vj : Set X)
      rw [pullback.condition, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ((pullback.snd Vi.ι Vj.ι).base n).2
  have hopen : IsOpen (e '' N) := he.isOpenMap _ hN
  obtain ⟨x, ⟨n, hn, rfl⟩, hxW⟩ : (e '' N ∩ (W : Set X)).Nonempty :=
    mem_closure_iff.mp (hcl (hmem n₀)) (e '' N) hopen ⟨n₀, hn₀, rfl⟩
  refine ⟨n, hn, ⟨⟨e n, hxW⟩, ?_⟩⟩
  apply he.injective
  change ((ℓ ≫ pullback.fst Vi.ι Vj.ι ≫ Vi.ι).base ⟨e n, hxW⟩) = e n
  rw [hℓι, Scheme.Opens.ι_apply]

theorem exists_glue {X Z S : Scheme.{u}} [IsReduced X] (p : X ⟶ S) (s : Z ⟶ S) [IsSeparated s]
    {I : Type*} (V : I → X.Opens) (hV : IsOpenCover V) (f : ∀ i, (V i : Scheme.{u}) ⟶ Z)
    (hf : ∀ i, f i ≫ s = (V i).ι ≫ p)
    (hagree : ∀ i j, ∃ (W : X.Opens) (hWi : W ≤ V i) (hWj : W ≤ V j),
      ((V i ⊓ V j : X.Opens) : Set X) ⊆ closure (W : Set X) ∧ X.homOfLE hWi ≫ f i = X.homOfLE hWj ≫ f j) :
    ∃ F : X ⟶ Z, (∀ i, (V i).ι ≫ F = f i) ∧ F ≫ s = p := by
  let 𝒰 := X.openCoverOfIsOpenCover V hV
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j := by
    intro i j
    change pullback.fst (V i).ι (V j).ι ≫ f i = pullback.snd (V i).ι (V j).ι ≫ f j
    obtain ⟨W, hWi, hWj, hcl, hW⟩ := hagree i j
    haveI : IsReduced (pullback (V i).ι (V j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (V i).ι (V j).ι ≫ (V i).ι)
    let ℓ := pullback.lift (f := (V i).ι) (g := (V j).ι) (X.homOfLE hWi) (X.homOfLE hWj)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    haveI : IsDominant ℓ := ⟨denseRange_lift (V i) (V j) W hWi hWj hcl⟩
    refine ext_of_isDominant_of_isSeparated s ?_ ℓ ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · change ℓ ≫ pullback.fst (V i).ι (V j).ι ≫ f i = ℓ ≫ pullback.snd (V i).ι (V j).ι ≫ f j
      rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hW]
  refine ⟨𝒰.glueMorphisms f hcompat, fun i => 𝒰.ι_glueMorphisms f hcompat i, ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact hf i

theorem exists_sup_extension {B Z S : Scheme.{u}} [IsReduced B] (p : B ⟶ S) (s : Z ⟶ S) [IsSeparated s]
    (D₁ D₂ : B.Opens) (M₁ : (D₁ : Scheme.{u}) ⟶ Z) (M₂ : (D₂ : Scheme.{u}) ⟶ Z)
    (hM₁ : M₁ ≫ s = D₁.ι ≫ p) (hM₂ : M₂ ≫ s = D₂.ι ≫ p)
    (W : B.Opens) (hW₁ : W ≤ D₁) (hW₂ : W ≤ D₂) (hcl : ((D₁ ⊓ D₂ : B.Opens) : Set B) ⊆ closure (W : Set B))
    (hagree : B.homOfLE hW₁ ≫ M₁ = B.homOfLE hW₂ ≫ M₂) :
    ∃ M : ((D₁ ⊔ D₂ : B.Opens) : Scheme.{u}) ⟶ Z,
      B.homOfLE (le_sup_left : D₁ ≤ D₁ ⊔ D₂) ≫ M = M₁ ∧
      B.homOfLE (le_sup_right : D₂ ≤ D₁ ⊔ D₂) ≫ M = M₂ ∧ M ≫ s = (D₁ ⊔ D₂).ι ≫ p := by
  set E : B.Opens := D₁ ⊔ D₂ with hE
  let V : Bool → (E : Scheme.{u}).Opens := fun b => bif b then E.ι ⁻¹ᵁ D₁ else E.ι ⁻¹ᵁ D₂
  have hVt : V true = E.ι ⁻¹ᵁ D₁ := rfl
  have hVf : V false = E.ι ⁻¹ᵁ D₂ := rfl
  have hV : IsOpenCover V := by
    rw [IsOpenCover, eq_top_iff]
    rintro ⟨x, hx⟩ -
    rw [Opens.mem_iSup]
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  haveI : IsReduced (E : Scheme.{u}) := isReduced_of_isOpenImmersion E.ι
  have hr₁ : Set.range ((V true).ι ≫ E.ι).base ⊆ Set.range D₁.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hr₂ : Set.range ((V false).ι ≫ E.ι).base ⊆ Set.range D₂.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  let g₁ : ((V true : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ D₁ := IsOpenImmersion.lift D₁.ι _ hr₁
  let g₂ : ((V false : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ D₂ := IsOpenImmersion.lift D₂.ι _ hr₂
  have hg₁ : g₁ ≫ D₁.ι = (V true).ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  have hg₂ : g₂ ≫ D₂.ι = (V false).ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  let f : ∀ b, ((V b : (E : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Z := fun b =>
    match b with
    | true => g₁ ≫ M₁
    | false => g₂ ≫ M₂
  have hft : f true = g₁ ≫ M₁ := rfl
  have hff : f false = g₂ ≫ M₂ := rfl
  have hf : ∀ b, f b ≫ s = (V b).ι ≫ (E.ι ≫ p) := by
    rintro (_ | _)
    · rw [hff, Category.assoc, hM₂, reassoc_of% hg₂]
    · rw [hft, Category.assoc, hM₁, reassoc_of% hg₁]
  let WE : (E : Scheme.{u}).Opens := E.ι ⁻¹ᵁ W
  have hWE₁ : WE ≤ V true := fun x hx => hW₁ hx
  have hWE₂ : WE ≤ V false := fun x hx => hW₂ hx
  have hclE : ((V true ⊓ V false : (E : Scheme.{u}).Opens) : Set E) ⊆ closure (WE : Set E) := by
    intro x hx
    have hx' : E.ι.base x ∈ ((D₁ ⊓ D₂ : B.Opens) : Set B) := hx
    rw [E.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    refine closure_mono ?_ (hcl hx')
    rintro y hyW
    exact ⟨⟨y, Or.inl (hW₁ hyW)⟩, hyW, rfl⟩
  have hrW : Set.range (WE.ι ≫ E.ι).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.2
  let w : (WE : Scheme.{u}) ⟶ W := IsOpenImmersion.lift W.ι _ hrW
  have hw : w ≫ W.ι = WE.ι ≫ E.ι := IsOpenImmersion.lift_fac _ _ _
  have hw₁ : (E : Scheme.{u}).homOfLE hWE₁ ≫ g₁ = w ≫ B.homOfLE hW₁ := by
    rw [← cancel_mono D₁.ι, Category.assoc, Category.assoc, hg₁, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, hw]
  have hw₂ : (E : Scheme.{u}).homOfLE hWE₂ ≫ g₂ = w ≫ B.homOfLE hW₂ := by
    rw [← cancel_mono D₂.ι, Category.assoc, Category.assoc, hg₂, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, hw]
  have hcross : (E : Scheme.{u}).homOfLE hWE₁ ≫ f true = (E : Scheme.{u}).homOfLE hWE₂ ≫ f false := by
    rw [hft, hff, reassoc_of% hw₁, reassoc_of% hw₂, hagree]
  have hagree' : ∀ b b', ∃ (W' : (E : Scheme.{u}).Opens) (hWi : W' ≤ V b) (hWj : W' ≤ V b'),
      ((V b ⊓ V b' : (E : Scheme.{u}).Opens) : Set E) ⊆ closure (W' : Set E) ∧
        (E : Scheme.{u}).homOfLE hWi ≫ f b = (E : Scheme.{u}).homOfLE hWj ≫ f b' := by
    rintro (_ | _) (_ | _)
    · exact ⟨V false, le_rfl, le_rfl, by rw [inf_idem]; exact subset_closure, rfl⟩
    · refine ⟨WE, hWE₂, hWE₁, ?_, hcross.symm⟩
      rw [inf_comm]; exact hclE
    · exact ⟨WE, hWE₁, hWE₂, hclE, hcross⟩
    · exact ⟨V true, le_rfl, le_rfl, by rw [inf_idem]; exact subset_closure, rfl⟩
  obtain ⟨F, hF, hFs⟩ := exists_glue (E.ι ≫ p) s V hV f hf hagree'
  have hs₁ : Set.range (B.homOfLE (le_sup_left : D₁ ≤ E)).base ⊆ Set.range (V true).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨d, rfl⟩
    change E.ι.base ((B.homOfLE _).base d) ∈ (D₁ : Set B)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply]
    exact d.2
  have hs₂ : Set.range (B.homOfLE (le_sup_right : D₂ ≤ E)).base ⊆ Set.range (V false).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨d, rfl⟩
    change E.ι.base ((B.homOfLE _).base d) ∈ (D₂ : Set B)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply]
    exact d.2
  let h₁ : (D₁ : Scheme.{u}) ⟶ V true := IsOpenImmersion.lift (V true).ι _ hs₁
  let h₂ : (D₂ : Scheme.{u}) ⟶ V false := IsOpenImmersion.lift (V false).ι _ hs₂
  have hh₁ : h₁ ≫ (V true).ι = B.homOfLE _ := IsOpenImmersion.lift_fac _ _ _
  have hh₂ : h₂ ≫ (V false).ι = B.homOfLE _ := IsOpenImmersion.lift_fac _ _ _
  have hid₁ : h₁ ≫ g₁ = 𝟙 _ := by
    rw [← cancel_mono D₁.ι, Category.assoc, hg₁, reassoc_of% hh₁, Scheme.homOfLE_ι, Category.id_comp]
  have hid₂ : h₂ ≫ g₂ = 𝟙 _ := by
    rw [← cancel_mono D₂.ι, Category.assoc, hg₂, reassoc_of% hh₂, Scheme.homOfLE_ι, Category.id_comp]
  refine ⟨F, ?_, ?_, hFs⟩
  · rw [← hh₁, Category.assoc, hF, hft, reassoc_of% hid₁]
  · rw [← hh₂, Category.assoc, hF, hff, reassoc_of% hid₂]

end GlueDense

section Setup

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

@[reassoc] theorem fst_y : pullback.fst y y ≫ y = pullback.snd y y ≫ y := pullback.condition

@[reassoc] theorem m_y : m.1 ≫ y = U.ι ≫ pullback.fst y y ≫ y := m.2

theorem m_eq_Phi_snd : m.1 = Phi y U m ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm

theorem universallyOpen_m [Smooth y] [IsOpenImmersion (Phi y U m)] : UniversallyOpen m.1 := by
  rw [m_eq_Phi_snd y U m]; infer_instance

variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

def jA : Y ⟶ pullback y y :=
  pullback.lift (y ≫ a) (𝟙 Y) (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

def kA : Y ⟶ pullback y y :=
  pullback.lift (𝟙 Y) (y ≫ a) (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)] theorem jA_fst : jA y a ha ≫ pullback.fst y y = y ≫ a := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem jA_snd : jA y a ha ≫ pullback.snd y y = 𝟙 Y := pullback.lift_snd _ _ _
@[reassoc (attr := simp)] theorem kA_fst : kA y a ha ≫ pullback.fst y y = 𝟙 Y := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem kA_snd : kA y a ha ≫ pullback.snd y y = y ≫ a := pullback.lift_snd _ _ _

theorem isPullback_jA : IsPullback (jA y a ha) y (pullback.fst y y) a := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (jA_fst y a ha)
    (IsPullback.of_hasPullback y y).flip
  rw [jA_snd, ha]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

theorem isPullback_kA : IsPullback (kA y a ha) y (pullback.snd y y) a := by
  refine IsPullback.of_right (h₁₂ := pullback.fst y y) (v₁₃ := y) (h₂₂ := y) ?_ (kA_snd y a ha)
    (IsPullback.of_hasPullback y y)
  rw [kA_fst, ha]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

scoped instance isClosedImmersion_jA [IsSeparated y] : IsClosedImmersion (jA y a ha) := by
  have : IsClosedImmersion (jA y a ha ≫ pullback.snd y y) := by rw [jA_snd]; infer_instance
  exact IsClosedImmersion.of_comp (jA y a ha) (pullback.snd y y)

scoped instance isClosedImmersion_kA [IsSeparated y] : IsClosedImmersion (kA y a ha) := by
  have : IsClosedImmersion (kA y a ha ≫ pullback.fst y y) := by rw [kA_fst]; infer_instance
  exact IsClosedImmersion.of_comp (kA y a ha) (pullback.fst y y)

def Ub : Y.Opens := jA y a ha ⁻¹ᵁ U

def Ua : Y.Opens := kA y a ha ⁻¹ᵁ U

def la : (Ua y U a ha : Scheme.{u}) ⟶ U := kA y a ha ∣_ U

@[reassoc] theorem la_ι : la y U a ha ≫ U.ι = (Ua y U a ha).ι ≫ kA y a ha := morphismRestrict_ι _ _

def rho : (Ua y U a ha : Scheme.{u}) ⟶ Y := la y U a ha ≫ m.1

@[reassoc] theorem rho_y : rho y U m a ha ≫ y = (Ua y U a ha).ι ≫ y := by
  rw [rho, Category.assoc, m.2, la_ι_assoc, kA_fst_assoc]

@[reassoc] theorem rho_kA : rho y U m a ha ≫ kA y a ha = la y U a ha ≫ Psi y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, kA_fst, Category.comp_id, Category.assoc, pullback.lift_fst, rho]
  · rw [Category.assoc, kA_snd, rho_y_assoc, Category.assoc, pullback.lift_snd, la_ι_assoc, kA_snd]

theorem isPullback_rho : IsPullback (rho y U m a ha) (la y U a ha) (kA y a ha) (Psi y U m) := by
  refine IsPullback.of_right (h₁₂ := y) (v₁₃ := a) (h₂₂ := pullback.snd y y) ?_ (rho_kA y U m a ha)
    (isPullback_kA y a ha).flip
  rw [rho_y, pullback.lift_snd]
  exact ((isPullback_morphismRestrict (kA y a ha) U).paste_vert (isPullback_kA y a ha)).flip

theorem isOpenImmersion_rho [IsOpenImmersion (Psi y U m)] : IsOpenImmersion (rho y U m a ha) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_rho y U m a ha).flip inferInstance

def Ya : (pullback y y).Opens := pullback.fst y y ⁻¹ᵁ Ua y U a ha

def bY : (Ya y U a ha : Scheme.{u}) ⟶ Ua y U a ha := pullback.fst y y ∣_ Ua y U a ha

@[reassoc] theorem bY_ι : bY y U a ha ≫ (Ua y U a ha).ι = (Ya y U a ha).ι ≫ pullback.fst y y :=
  morphismRestrict_ι _ _

def Θ : (Ya y U a ha : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (bY y U a ha ≫ rho y U m a ha) ((Ya y U a ha).ι ≫ pullback.snd y y)
    (by rw [Category.assoc, rho_y, bY_ι_assoc, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem Θ_fst : Θ y U m a ha ≫ pullback.fst y y = bY y U a ha ≫ rho y U m a ha := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Θ_snd : Θ y U m a ha ≫ pullback.snd y y = (Ya y U a ha).ι ≫ pullback.snd y y :=
  pullback.lift_snd _ _ _

theorem Θ_fst_y : Θ y U m a ha ≫ pullback.fst y y ≫ y = (Ya y U a ha).ι ≫ pullback.fst y y ≫ y := by
  rw [Θ_fst_assoc, rho_y, bY_ι_assoc]

theorem isPullback_Θ : IsPullback (Θ y U m a ha) (bY y U a ha) (pullback.fst y y) (rho y U m a ha) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (Θ_fst y U m a ha)
    (IsPullback.of_hasPullback y y).flip
  rw [Θ_snd, rho_y]
  exact (isPullback_morphismRestrict (pullback.fst y y) (Ua y U a ha)).flip.paste_horiz
    (IsPullback.of_hasPullback y y).flip

theorem isOpenImmersion_Θ [IsOpenImmersion (Psi y U m)] : IsOpenImmersion (Θ y U m a ha) :=
  haveI := isOpenImmersion_rho y U m a ha
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_Θ y U m a ha).flip inferInstance

def V2 : (Ya y U a ha : Scheme.{u}).Opens := Θ y U m a ha ⁻¹ᵁ U

def U2 : (pullback y y).Opens := (Ya y U a ha).ι ''ᵁ V2 y U m a ha

def θ : (V2 y U m a ha : Scheme.{u}) ⟶ U := Θ y U m a ha ∣_ U

@[reassoc] theorem θ_ι : θ y U m a ha ≫ U.ι = (V2 y U m a ha).ι ≫ Θ y U m a ha := morphismRestrict_ι _ _

def eV : (V2 y U m a ha : Scheme.{u}) ≅ (U2 y U m a ha : Scheme.{u}) := (Ya y U a ha).ι.isoImage _

@[reassoc] theorem eV_hom_ι : (eV y U m a ha).hom ≫ (U2 y U m a ha).ι = (V2 y U m a ha).ι ≫ (Ya y U a ha).ι :=
  Scheme.Hom.isoImage_hom_ι _ _

@[reassoc] theorem eV_inv_ι : (eV y U m a ha).inv ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι = (U2 y U m a ha).ι :=
  Scheme.Hom.isoImage_inv_ι _ _

end Setup

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
      (pullback.fst y' y') ⁻¹' Set.range i₁.1 ∩ (pullback.snd y' y') ⁻¹' Set.range i₂.1 :=
by
  unfold ch; exact Scheme.Pullback.range_map y y y' y' i₁.1 i₂.1 (𝟙 _) _ _

theorem ch_fst_y' : ch y y' i₁ i₂ ≫ pullback.fst y' y' ≫ y' = pullback.fst y y ≫ y := by
  rw [ch_fst_assoc, i₁.2]

end Charts

section Translate

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

theorem dense_fibre_jA [IsSeparated y] (S : Set ↑(pullback y y)) (s : Spec (CommRingCat.of R))
    (hS : Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) := by
  have hainj : Function.Injective a.base := by
    intro s₁ s₂ h
    have := congrArg y.base h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha] at this
  let φ : {b : ↑Y // y.base b = s} → {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} :=
    fun b => ⟨(jA y a ha).base b.1, by rw [← Scheme.Hom.comp_apply, jA_fst, Scheme.Hom.comp_apply, b.2]⟩
  have hφc : Continuous φ := ((jA y a ha).base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Topology.IsInducing φ := by
    refine Topology.IsInducing.of_comp hφc continuous_subtype_val ?_
    exact (jA y a ha).isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hE : pullback.fst (pullback.fst y y) a =
      (pullback.fst (pullback.fst y y) a ≫ pullback.snd y y) ≫ jA y a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, jA_fst, pullback.condition, Category.assoc, ← pullback.condition_assoc,
        reassoc_of% (pullback.condition (f := pullback.fst y y) (g := a)), reassoc_of% ha]
    · rw [Category.assoc, jA_snd, Category.comp_id]
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ : q ∈ Set.range (pullback.fst (pullback.fst y y) a).base := by
      rw [Scheme.Pullback.range_fst]; exact ⟨s, hq.symm⟩
    refine ⟨⟨(pullback.snd y y).base q, hainj ?_⟩, ?_⟩
    · change a.base (y.base ((pullback.snd y y).base q)) = a.base s
      congr 1
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ha]
      rfl
    · apply Subtype.ext
      change (jA y a ha).base ((pullback.snd y y).base q) = q
      conv_rhs => rw [← hz, hE]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  have hpre : ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) =
      φ ⁻¹' ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} → ↑(pullback y y)) ⁻¹' S) :=
    rfl
  rw [hpre, hφi.dense_iff]
  intro b
  rw [Set.image_preimage_eq _ hφs, hS.closure_eq]
  exact Set.mem_univ _

theorem dense_Ub [IsSeparated y]
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense ((Ub y U a ha : Y.Opens) : Set Y) :=
  dense_of_forall_dense_fibre (fun b => y.base b) _ fun s => dense_fibre_jA y a ha _ s (hU₁ _)

variable {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)

abbrev sA : pullback y y ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y)
    (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
      (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
    (pullback.snd y y)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id, pullback.condition])

abbrev grm : (U : Scheme.{u}) ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

variable (g₀ : (U : Scheme.{u}) ⟶ G) (hg₀ : g₀ ≫ γ = grm y U m)

def mkΓa {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    T ⟶ pullback γ (sA y a ha) :=
  pullback.lift (w ≫ g₀)
    (pullback.lift (f := y) (g := y) x (w ≫ m.1)
      (by rw [Category.assoc, m.2, ← h2, Category.assoc, Category.assoc, pullback.condition]))
    (by
      rw [Category.assoc, hg₀]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
          exact h1
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
          exact h2
      · simp only [Category.assoc, pullback.lift_snd])

theorem mkΓa_pτ {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m a ha γ g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.fst y y = x := by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_fst]

theorem mkΓa_pι {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m a ha γ g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.snd y y = w ≫ m.1 := by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_snd]

include hg₀ in

theorem translate {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y')
    (hΓa : pullback.snd γ (sA y a ha) ≫ pullback.fst y y ≫ τ.1 = pullback.snd γ (sA y a ha) ≫ pullback.snd y y ≫ ι.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (hx : x ≫ y = t) (w : T ⟶ (U : Scheme.{u}))
    (hw₁ : w ≫ U.ι ≫ pullback.fst y y = t ≫ a) (hw₂ : w ≫ U.ι ≫ pullback.snd y y = x) :
    x ≫ τ.1 = w ≫ m.1 ≫ ι.1 := by
  have h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a := by rw [hw₁, reassoc_of% hx]
  rw [← mkΓa_pτ y U m a ha γ g₀ hg₀ x w h1 hw₂, Category.assoc, Category.assoc, hΓa, ← Category.assoc,
    ← Category.assoc, Category.assoc _ (pullback.snd γ (sA y a ha)), mkΓa_pι, Category.assoc]

end Translate

section Core

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1]
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)

include hassoc htr in

theorem core01 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u₀ u₁ wa wq : T ⟶ (U : Scheme.{u}))
    (ht₁ : u₁ ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (h1 : u₀ ≫ U.ι ≫ pullback.fst y y ≫ ι.1 = u₁ ≫ U.ι ≫ pullback.fst y y ≫ τ.1)
    (h2 : u₀ ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.snd y y)
    (hwa : wa ≫ U.ι = (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a ha)
    (hwq : wq ≫ U.ι = (u₁ ≫ m.1) ≫ jA y a ha) :
    u₀ ≫ m.1 ≫ ι.1 = u₁ ≫ m.1 ≫ τ.1 := by
  have hwa₁ : wa ≫ U.ι ≫ pullback.fst y y = t ≫ a := by
    rw [reassoc_of% hwa, jA_fst, reassoc_of% ht₁]
  have hwa₂ : wa ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hwa, jA_snd, Category.comp_id]
  have hm₁ : (u₁ ≫ m.1) ≫ y = t := by rw [Category.assoc, m.2, ht₁]
  have hwq₁ : wq ≫ U.ι ≫ pullback.fst y y = t ≫ a := by
    rw [reassoc_of% hwq, jA_fst, reassoc_of% hm₁]
  have hwq₂ : wq ≫ U.ι ≫ pullback.snd y y = u₁ ≫ m.1 := by
    rw [reassoc_of% hwq, jA_snd, Category.comp_id]

  have e1 : (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ τ.1 = wa ≫ m.1 ≫ ι.1 :=
    htr t _ (by rw [Category.assoc, Category.assoc, ht₁]) wa hwa₁ hwa₂
  have hb : u₀ ≫ U.ι ≫ pullback.fst y y = wa ≫ m.1 := by
    rw [← cancel_mono ι.1]
    simp only [Category.assoc] at e1 ⊢
    rw [h1, e1]

  have e2 : (u₁ ≫ m.1) ≫ τ.1 = wq ≫ m.1 ≫ ι.1 := htr t _ hm₁ wq hwq₁ hwq₂

  have hu₀ : u₀ ≫ U.ι ≫ pullback.fst y y ≫ y = t := by
    rw [reassoc_of% hb, m.2, reassoc_of% hwa₁, ha, Category.comp_id]
  have hwa₀ : wa ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwa₁, ha, Category.comp_id]
  have hwq₀ : wq ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwq₁, ha, Category.comp_id]
  have key := hassoc t ⟨wa, hwa₀⟩ ⟨u₁, ht₁⟩ ⟨u₀, hu₀⟩ ⟨wq, hwq₀⟩ hwa₂ hb h2 (by rw [hwq₁, hwa₁]) hwq₂
  change u₀ ≫ m.1 = wq ≫ m.1 at key
  rw [reassoc_of% key, ← e2, Category.assoc]

include hassoc htr in

theorem core02 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u₀ ub v wd : T ⟶ (U : Scheme.{u}))
    (ht : ub ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (hub : ub ≫ U.ι ≫ pullback.snd y y = t ≫ a) (hv₁ : v ≫ U.ι ≫ pullback.fst y y = ub ≫ m.1)
    (h1 : u₀ ≫ U.ι ≫ pullback.fst y y = ub ≫ U.ι ≫ pullback.fst y y)
    (h2 : u₀ ≫ U.ι ≫ pullback.snd y y ≫ ι.1 = (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1)
    (hwd : wd ≫ U.ι = (v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a ha) :
    u₀ ≫ m.1 = v ≫ m.1 := by
  have hv₀ : v ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hv₁, m.2, ht]
  have hd : (v ≫ U.ι ≫ pullback.snd y y) ≫ y = t := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, hv₀]
  have hwd₁ : wd ≫ U.ι ≫ pullback.fst y y = t ≫ a := by rw [reassoc_of% hwd, jA_fst, reassoc_of% hd]
  have hwd₂ : wd ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.snd y y := by
    rw [reassoc_of% hwd, jA_snd, Category.comp_id]
  have e1 : (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1 = wd ≫ m.1 ≫ ι.1 := htr t _ hd wd hwd₁ hwd₂
  have hd₀ : u₀ ≫ U.ι ≫ pullback.snd y y = wd ≫ m.1 := by
    rw [← cancel_mono ι.1, Category.assoc, Category.assoc, h2, e1, Category.assoc]
  have hu₀ : u₀ ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% h1, ht]
  have hwd₀ : wd ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hwd₁, ha, Category.comp_id]
  have key := hassoc t ⟨ub, ht⟩ ⟨wd, hwd₀⟩ ⟨v, hv₀⟩ ⟨u₀, hu₀⟩ (by rw [hub, hwd₁]) hv₁ hwd₂.symm h1 hd₀
  exact key.symm

end Core

section Pieces

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y')
  [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

def P0 : (pullback y' y').Opens := ch y y' ι ι ''ᵁ U

def P1 : (pullback y' y').Opens := ch y y' τ ι ''ᵁ U

def P2 : (pullback y' y').Opens := ch y y' ι τ ''ᵁ U2 y U m a ha

def e0 : (U : Scheme.{u}) ≅ (P0 y U y' ι : Scheme.{u}) := (ch y y' ι ι).isoImage U

def e1 : (U : Scheme.{u}) ≅ (P1 y U y' ι τ : Scheme.{u}) := (ch y y' τ ι).isoImage U

def e2 : (U2 y U m a ha : Scheme.{u}) ≅ (P2 y U m a ha y' ι τ : Scheme.{u}) := (ch y y' ι τ).isoImage _

@[reassoc] theorem e0_inv_ι : (e0 y U y' ι).inv ≫ U.ι ≫ ch y y' ι ι = (P0 y U y' ι).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc] theorem e0_hom_ι : (e0 y U y' ι).hom ≫ (P0 y U y' ι).ι = U.ι ≫ ch y y' ι ι :=
  Scheme.Hom.isoImage_hom_ι _ _
@[reassoc] theorem e1_inv_ι : (e1 y U y' ι τ).inv ≫ U.ι ≫ ch y y' τ ι = (P1 y U y' ι τ).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc] theorem e1_hom_ι : (e1 y U y' ι τ).hom ≫ (P1 y U y' ι τ).ι = U.ι ≫ ch y y' τ ι :=
  Scheme.Hom.isoImage_hom_ι _ _
@[reassoc] theorem e2_inv_ι :
    (e2 y U m a ha y' ι τ).inv ≫ (U2 y U m a ha).ι ≫ ch y y' ι τ = (P2 y U m a ha y' ι τ).ι :=
  Scheme.Hom.isoImage_inv_ι _ _
@[reassoc] theorem e2_hom_ι :
    (e2 y U m a ha y' ι τ).hom ≫ (P2 y U m a ha y' ι τ).ι = (U2 y U m a ha).ι ≫ ch y y' ι τ :=
  Scheme.Hom.isoImage_hom_ι _ _

def f0 : (P0 y U y' ι : Scheme.{u}) ⟶ Y' := (e0 y U y' ι).inv ≫ m.1 ≫ ι.1

def f1 : (P1 y U y' ι τ : Scheme.{u}) ⟶ Y' := (e1 y U y' ι τ).inv ≫ m.1 ≫ τ.1

def f2 : (P2 y U m a ha y' ι τ : Scheme.{u}) ⟶ Y' :=
  (e2 y U m a ha y' ι τ).inv ≫ (eV y U m a ha).inv ≫ θ y U m a ha ≫ m.1 ≫ ι.1

theorem f0_y' : f0 y U m y' ι ≫ y' = (P0 y U y' ι).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f0, Category.assoc, Category.assoc, ι.2, m.2, ← e0_inv_ι_assoc, ch_fst_assoc, ι.2]

theorem f1_y' : f1 y U m y' ι τ ≫ y' = (P1 y U y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f1, Category.assoc, Category.assoc, τ.2, m.2, ← e1_inv_ι_assoc, ch_fst_assoc, τ.2]

theorem f2_y' : f2 y U m a ha y' ι τ ≫ y' = (P2 y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  rw [f2, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ι.2, m.2, θ_ι_assoc, Θ_fst_y,
    ← e2_inv_ι_assoc, ch_fst_assoc, ι.2, ← eV_inv_ι_assoc]

end Pieces

section Agree

variable {R : Type u} [CommRing R]
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y')
  [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

def U01 : (pullback y y).Opens := (pullback.fst y y ⁻¹ᵁ Ub y U a ha) ⊓ U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha)

def U2' : (pullback y y).Opens := U2 y U m a ha ⊓ (pullback.snd y y ⁻¹ᵁ Ub y U a ha)

def W01 : (pullback y' y').Opens := P0 y U y' ι ⊓ ch y y' τ ι ''ᵁ U01 y U m a ha

def W02 : (pullback y' y').Opens := P0 y U y' ι ⊓ ch y y' ι τ ''ᵁ U2' y U m a ha

theorem W01_le_P0 : W01 y U m a ha y' ι τ ≤ P0 y U y' ι := inf_le_left
theorem W01_le_P1 : W01 y U m a ha y' ι τ ≤ P1 y U y' ι τ :=
  le_trans inf_le_right ((Scheme.Hom.image_le_image_iff _ _ _).mpr inf_le_right |>.trans
    ((Scheme.Hom.image_le_image_iff _ _ _).mpr (by
      intro q hq
      have hq' : q ∈ ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set _) := hq
      rw [Scheme.Hom.coe_image] at hq'
      obtain ⟨u, -, rfl⟩ := hq'
      exact u.2)))
theorem W02_le_P0 : W02 y U m a ha y' ι τ ≤ P0 y U y' ι := inf_le_left
theorem W02_le_P2 : W02 y U m a ha y' ι τ ≤ P2 y U m a ha y' ι τ :=
  le_trans inf_le_right ((Scheme.Hom.image_le_image_iff _ _ _).mpr inf_le_left)

variable (hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
      (U : Set ↑(pullback y y))))

include hU₁ in

theorem subset_closure_U01 [Smooth y] [IsSeparated y] [IsOpenImmersion (Phi y U m)] :
    (U : Set ↑(pullback y y)) ⊆ closure (U01 y U m a ha : Set ↑(pullback y y)) := by
  have hUb : Dense ((Ub y U a ha : Y.Opens) : Set Y) := dense_Ub y U a ha hU₁
  haveI := universallyOpen_m y U m
  have hA : Dense ((pullback.fst y y ⁻¹ᵁ Ub y U a ha : (pullback y y).Opens) : Set ↑(pullback y y)) :=
    hUb.preimage (pullback.fst y y).isOpenMap
  have hD : Dense ((m.1 ⁻¹ᵁ Ub y U a ha : (U : Scheme.{u}).Opens) : Set ↑(U : Scheme.{u})) :=
    hUb.preimage m.1.isOpenMap
  have hA' : (U : Set ↑(pullback y y)) ⊆
      closure ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set ↑(pullback y y)) := by
    rw [Scheme.Hom.coe_image, ← Scheme.Opens.range_ι U, ← Set.image_univ, ← hD.closure_eq]
    exact image_closure_subset_closure_image U.ι.continuous
  simp only [U01, Opens.coe_inf]
  exact subset_closure_inter U.isOpen (Opens.isOpen _) (Dense.mono (fun _ h => h) hA |>.closure_eq ▸
    fun _ _ => Set.mem_univ _) hA'

include hU₁ in

theorem subset_closure_U2' [Smooth y] [IsSeparated y] :
    (U2 y U m a ha : Set ↑(pullback y y)) ⊆ closure (U2' y U m a ha : Set ↑(pullback y y)) := by
  have hUb : Dense ((Ub y U a ha : Y.Opens) : Set Y) := dense_Ub y U a ha hU₁
  have hA : Dense ((pullback.snd y y ⁻¹ᵁ Ub y U a ha : (pullback y y).Opens) : Set ↑(pullback y y)) :=
    hUb.preimage (pullback.snd y y).isOpenMap
  simp only [U2', Opens.coe_inf]
  intro q hq
  have := (U2 y U m a ha).isOpen.inter_closure (t := ((pullback.snd y y ⁻¹ᵁ Ub y U a ha : (pullback y y).Opens) : Set _))
  exact this ⟨hq, hA.closure_eq ▸ Set.mem_univ q⟩

include hU₁ in
theorem closure_W01 [Smooth y] [IsSeparated y] [IsOpenImmersion (Phi y U m)] :
    ((P0 y U y' ι ⊓ P1 y U y' ι τ : (pullback y' y').Opens) : Set ↑(pullback y' y')) ⊆
      closure (W01 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
  simp only [W01, P1, Opens.coe_inf, Scheme.Hom.coe_image]
  exact inter_image_subset_closure (ch y y' τ ι).continuous (P0 y U y' ι).isOpen (subset_closure_U01 y U m a ha hU₁)

include hU₁ in
theorem closure_W02 [Smooth y] [IsSeparated y] :
    ((P0 y U y' ι ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set ↑(pullback y' y')) ⊆
      closure (W02 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
  simp only [W02, P2, Opens.coe_inf, Scheme.Hom.coe_image]
  exact inter_image_subset_closure (ch y y' ι τ).continuous (P0 y U y' ι).isOpen (subset_closure_U2' y U m a ha hU₁)

variable
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)

include hassoc htr in

theorem agree01 :
    (pullback y' y').homOfLE (W01_le_P0 y U m a ha y' ι τ) ≫ f0 y U m y' ι =
      (pullback y' y').homOfLE (W01_le_P1 y U m a ha y' ι τ) ≫ f1 y U m y' ι τ := by
  set W := W01 y U m a ha y' ι τ
  set u₀ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W01_le_P0 y U m a ha y' ι τ) ≫ (e0 y U y' ι).inv
  set u₁ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W01_le_P1 y U m a ha y' ι τ) ≫ (e1 y U y' ι τ).inv
  have hu₀ : u₀ ≫ U.ι ≫ ch y y' ι ι = W.ι := by rw [Category.assoc, e0_inv_ι, Scheme.homOfLE_ι]
  have hu₁ : u₁ ≫ U.ι ≫ ch y y' τ ι = W.ι := by rw [Category.assoc, e1_inv_ι, Scheme.homOfLE_ι]
  have h1 : u₀ ≫ U.ι ≫ pullback.fst y y ≫ ι.1 = u₁ ≫ U.ι ≫ pullback.fst y y ≫ τ.1 := by
    have := congrArg (· ≫ pullback.fst y' y') (hu₀.trans hu₁.symm)
    simpa only [Category.assoc, ch_fst] using this
  have h2 : u₀ ≫ U.ι ≫ pullback.snd y y = u₁ ≫ U.ι ≫ pullback.snd y y := by
    have := congrArg (· ≫ pullback.snd y' y') (hu₀.trans hu₁.symm)
    simp only [Category.assoc, ch_snd] at this
    simpa only [← Category.assoc, cancel_mono] using this

  have hW : Set.range (u₁ ≫ U.ι).base ⊆ (U01 y U m a ha : Set ↑(pullback y y)) := by
    rintro _ ⟨w, rfl⟩
    have hw : W.ι.base w ∈ ((ch y y' τ ι ''ᵁ U01 y U m a ha : (pullback y' y').Opens) : Set _) := w.2.2
    rw [Scheme.Hom.coe_image] at hw
    obtain ⟨q, hq, hqw⟩ := hw
    rw [← hu₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hqw
    rw [Scheme.Hom.comp_apply, ← (ch y y' τ ι).isOpenEmbedding.injective hqw]
    exact hq
  have hra : Set.range ((u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have := (hW ⟨w, rfl⟩).1
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  have hrq : Set.range ((u₁ ≫ m.1) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have h := (hW ⟨w, rfl⟩).2
    have h' : (U.ι.base (u₁.base w)) ∈ ((U.ι ''ᵁ (m.1 ⁻¹ᵁ Ub y U a ha) : (pullback y y).Opens) : Set _) := by
      simpa only [Scheme.Hom.comp_apply] using h
    rw [Scheme.Hom.coe_image] at h'
    obtain ⟨u, hu, huw⟩ := h'
    have hu' : u = u₁.base w := U.ι.isOpenEmbedding.injective huw
    subst hu'
    simp only [Scheme.Hom.comp_apply] at hu
    exact hu
  obtain ⟨wa, hwa⟩ : ∃ wa : (W : Scheme.{u}) ⟶ U, wa ≫ U.ι = (u₁ ≫ U.ι ≫ pullback.fst y y) ≫ jA y a ha :=
    ⟨IsOpenImmersion.lift U.ι _ hra, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨wq, hwq⟩ : ∃ wq : (W : Scheme.{u}) ⟶ U, wq ≫ U.ι = (u₁ ≫ m.1) ≫ jA y a ha :=
    ⟨IsOpenImmersion.lift U.ι _ hrq, IsOpenImmersion.lift_fac _ _ _⟩
  have key := core01 y U m a ha ι τ hassoc htr (u₁ ≫ U.ι ≫ pullback.fst y y ≫ y) u₀ u₁ wa wq rfl h1 h2 hwa hwq
  change u₀ ≫ m.1 ≫ ι.1 = u₁ ≫ m.1 ≫ τ.1 at key
  simp only [f0, f1, u₀, u₁, Category.assoc] at key ⊢
  exact key

include hassoc htr in

theorem agree02 :
    (pullback y' y').homOfLE (W02_le_P0 y U m a ha y' ι τ) ≫ f0 y U m y' ι =
      (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ f2 y U m a ha y' ι τ := by
  set W := W02 y U m a ha y' ι τ
  set u₀ : (W : Scheme.{u}) ⟶ U := (pullback y' y').homOfLE (W02_le_P0 y U m a ha y' ι τ) ≫ (e0 y U y' ι).inv
  set p₂ : (W : Scheme.{u}) ⟶ V2 y U m a ha :=
    (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m a ha).inv
  set ub : (W : Scheme.{u}) ⟶ U := p₂ ≫ (V2 y U m a ha).ι ≫ bY y U a ha ≫ la y U a ha
  set v : (W : Scheme.{u}) ⟶ U := p₂ ≫ θ y U m a ha
  have hu₀ : u₀ ≫ U.ι ≫ ch y y' ι ι = W.ι := by rw [Category.assoc, e0_inv_ι, Scheme.homOfLE_ι]
  have hp₂ : p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ ch y y' ι τ = W.ι := by
    rw [Category.assoc, Category.assoc, eV_inv_ι_assoc, e2_inv_ι, Scheme.homOfLE_ι]

  have hubι : ub ≫ U.ι = (p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y) ≫ kA y a ha := by
    simp only [ub, Category.assoc, la_ι, bY_ι_assoc]
  have hub₁ : ub ≫ U.ι ≫ pullback.fst y y = p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y := by
    rw [reassoc_of% hubι, kA_fst, Category.comp_id]
  set t : (W : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y ≫ y
  have ht : ub ≫ U.ι ≫ pullback.fst y y ≫ y = t := by rw [reassoc_of% hub₁]
  have hub₂ : ub ≫ U.ι ≫ pullback.snd y y = t ≫ a := by
    rw [reassoc_of% hubι, kA_snd]; simp only [t, Category.assoc]
  have hv₁ : v ≫ U.ι ≫ pullback.fst y y = ub ≫ m.1 := by
    simp only [v, ub, Category.assoc, θ_ι_assoc, Θ_fst, rho]
  have hv₂ : v ≫ U.ι ≫ pullback.snd y y = p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.snd y y := by
    simp only [v, Category.assoc, θ_ι_assoc, Θ_snd]
  have h1 : u₀ ≫ U.ι ≫ pullback.fst y y = ub ≫ U.ι ≫ pullback.fst y y := by
    have := congrArg (· ≫ pullback.fst y' y') (hu₀.trans hp₂.symm)
    simp only [Category.assoc, ch_fst] at this
    rw [hub₁]
    simpa only [← Category.assoc, cancel_mono] using this
  have h2 : u₀ ≫ U.ι ≫ pullback.snd y y ≫ ι.1 = (v ≫ U.ι ≫ pullback.snd y y) ≫ τ.1 := by
    have := congrArg (· ≫ pullback.snd y' y') (hu₀.trans hp₂.symm)
    simp only [Category.assoc, ch_snd] at this
    rw [this, hv₂]; simp only [Category.assoc]

  have hW : Set.range (p₂ ≫ (V2 y U m a ha).ι ≫ (Ya y U a ha).ι).base ⊆ (U2' y U m a ha : Set ↑(pullback y y)) := by
    rintro _ ⟨w, rfl⟩
    have hw : W.ι.base w ∈ ((ch y y' ι τ ''ᵁ U2' y U m a ha : (pullback y' y').Opens) : Set _) := w.2.2
    rw [Scheme.Hom.coe_image] at hw
    obtain ⟨q, hq, hqw⟩ := hw
    rw [← hp₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hqw
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← (ch y y' ι τ).isOpenEmbedding.injective hqw]
    exact hq
  have hrd : Set.range ((v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a ha).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, hv₂]
    rintro _ ⟨w, rfl⟩
    have := (hW ⟨w, rfl⟩).2
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  obtain ⟨wd, hwd⟩ : ∃ wd : (W : Scheme.{u}) ⟶ U, wd ≫ U.ι = (v ≫ U.ι ≫ pullback.snd y y) ≫ jA y a ha :=
    ⟨IsOpenImmersion.lift U.ι _ hrd, IsOpenImmersion.lift_fac _ _ _⟩
  have key := core02 y U m a ha ι τ hassoc htr t u₀ ub v wd ht hub₂ hv₁ h1 h2 hwd
  have goal : u₀ ≫ m.1 ≫ ι.1 = v ≫ m.1 ≫ ι.1 := by rw [reassoc_of% key]
  simp only [f0, f2, u₀, v, p₂, Category.assoc] at goal ⊢
  exact goal

end Agree

section Law

variable {R : Type u} [CommRing R]
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

abbrev U' : (pullback y' y').Opens := (P0 y U y' ι ⊔ P1 y U y' ι τ) ⊔ P2 y U m a ha y' ι τ

theorem P0_le : P0 y U y' ι ≤ U' y U m a ha y' ι τ := le_sup_left.trans le_sup_left
theorem P1_le : P1 y U y' ι τ ≤ U' y U m a ha y' ι τ := le_sup_right.trans le_sup_left
theorem P2_le : P2 y U m a ha y' ι τ ≤ U' y U m a ha y' ι τ := le_sup_right

theorem dense_image_ch [Smooth y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsNoetherianRing R]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    {S : Set ↑(pullback y y)} (hS : Dense S) : Dense ((ch y y' ι ι) '' S) := by
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian y'
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace y'
  haveI : IsNoetherian Y' := {}
  have hd : Dense (Set.range ι.1.base) :=
    dense_of_forall_maximal_mem fun p hp => hιd p fun p' h _ => hp p' h
  have hr : Dense (Set.range (ch y y' ι ι)) := by
    rw [range_ch]
    exact (hd.preimage (pullback.fst y' y').isOpenMap).inter_of_isOpen_left
      (hd.preimage (pullback.snd y' y').isOpenMap)
      ((pullback.fst y' y').continuous.isOpen_preimage _ ι.1.isOpenEmbedding.isOpen_range)
  have h1 : Set.range (ch y y' ι ι) ⊆ closure ((ch y y' ι ι) '' S) := by
    rw [← Set.image_univ, ← hS.closure_eq]
    exact image_closure_subset_closure_image (ch y y' ι ι).continuous
  intro z
  exact (closure_minimal h1 isClosed_closure) (hr.closure_eq ▸ Set.mem_univ z)

variable
  (hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
      (U : Set ↑(pullback y y))))
  (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1)
  (htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
    w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1)
  (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)

include hU₁ hassoc htr hιd in

theorem exists_law [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y]
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y'] [IsOpenImmersion (Phi y U m)] :
    ∃ M : (U' y U m a ha y' ι τ : Scheme.{u}) ⟶ Y',
      (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ) ≫ M = f0 y U m y' ι ∧
      (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ) ≫ M = f1 y U m y' ι τ ∧
      (pullback y' y').homOfLE (P2_le y U m a ha y' ι τ) ≫ M = f2 y U m a ha y' ι τ ∧
      M ≫ y' = (U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y' := by
  haveI : IsReduced (pullback y' y') :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst y' y' ≫ y')

  obtain ⟨M₁, hM₁0, hM₁1, hM₁y⟩ := exists_sup_extension (pullback.fst y' y' ≫ y') y'
    (P0 y U y' ι) (P1 y U y' ι τ) (f0 y U m y' ι) (f1 y U m y' ι τ) (f0_y' y U m y' ι) (f1_y' y U m y' ι τ)
    (W01 y U m a ha y' ι τ) (W01_le_P0 y U m a ha y' ι τ) (W01_le_P1 y U m a ha y' ι τ)
    (closure_W01 y U m a ha y' ι τ hU₁) (agree01 y U m a ha y' ι τ hassoc htr)

  have hW : W02 y U m a ha y' ι τ ≤ P0 y U y' ι ⊔ P1 y U y' ι τ := (W02_le_P0 y U m a ha y' ι τ).trans le_sup_left
  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  have hP0 : Dense ((P0 y U y' ι : (pullback y' y').Opens) : Set ↑(pullback y' y')) := by
    rw [P0, Scheme.Hom.coe_image]; exact dense_image_ch y y' ι hιd hU
  have hcl : (((P0 y U y' ι ⊔ P1 y U y' ι τ) ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set _) ⊆
      closure (W02 y U m a ha y' ι τ : Set ↑(pullback y' y')) := by
    intro q hq
    have h1 : q ∈ closure (((P0 y U y' ι ⊓ P2 y U m a ha y' ι τ : (pullback y' y').Opens) : Set _)) := by
      rw [Opens.coe_inf, Set.inter_comm]
      exact (P2 y U m a ha y' ι τ).isOpen.inter_closure ⟨hq.2, hP0.closure_eq ▸ Set.mem_univ q⟩
    exact (closure_minimal (closure_W02 y U m a ha y' ι τ hU₁) isClosed_closure) h1
  have hagree : (pullback y' y').homOfLE hW ≫ M₁ =
      (pullback y' y').homOfLE (W02_le_P2 y U m a ha y' ι τ) ≫ f2 y U m a ha y' ι τ := by
    rw [← agree02 y U m a ha y' ι τ hassoc htr, ← hM₁0, ← Category.assoc, Scheme.homOfLE_homOfLE]
  obtain ⟨M, hM01, hM2, hMy⟩ := exists_sup_extension (pullback.fst y' y' ≫ y') y'
    (P0 y U y' ι ⊔ P1 y U y' ι τ) (P2 y U m a ha y' ι τ) M₁ (f2 y U m a ha y' ι τ) hM₁y (f2_y' y U m a ha y' ι τ)
    (W02 y U m a ha y' ι τ) hW (W02_le_P2 y U m a ha y' ι τ) hcl hagree
  refine ⟨M, ?_, ?_, hM2, hMy⟩
  · rw [← hM₁0, ← hM01, ← Category.assoc, Scheme.homOfLE_homOfLE]
  · rw [← hM₁1, ← hM01, ← Category.assoc, Scheme.homOfLE_homOfLE]

end Law

section Clauses

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
  (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
  (M : (U' y U m a ha y' ι τ : Scheme.{u}) ⟶ Y')
  (hM0 : (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ) ≫ M = f0 y U m y' ι)
  (hM1 : (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ) ≫ M = f1 y U m y' ι τ)
  (hM2 : (pullback y' y').homOfLE (P2_le y U m a ha y' ι τ) ≫ M = f2 y U m a ha y' ι τ)

include hM0 in

theorem clause0 {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}), w' ≫ (U' y U m a ha y' ι τ).ι = w ≫ U.ι ≫ ch y y' ι ι ∧ w' ≫ M = w ≫ m.1 ≫ ι.1 := by
  refine ⟨w ≫ (e0 y U y' ι).hom ≫ (pullback y' y').homOfLE (P0_le y U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, e0_hom_ι]
  · rw [Category.assoc, Category.assoc, hM0, f0, Iso.hom_inv_id_assoc]

include hM1 in

theorem clause1 {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}), w' ≫ (U' y U m a ha y' ι τ).ι = w ≫ U.ι ≫ ch y y' τ ι ∧ w' ≫ M = w ≫ m.1 ≫ τ.1 := by
  refine ⟨w ≫ (e1 y U y' ι τ).hom ≫ (pullback y' y').homOfLE (P1_le y U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, e1_hom_ι]
  · rw [Category.assoc, Category.assoc, hM1, f1, Iso.hom_inv_id_assoc]

include hM2 in

theorem clause2 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : T ⟶ Y) (hd : d ≫ y = t)
    (u v : T ⟶ (U : Scheme.{u})) (hut : u ≫ U.ι ≫ pullback.fst y y ≫ y = t)
    (hu : u ≫ U.ι ≫ pullback.snd y y = t ≫ a) (hv₁ : v ≫ U.ι ≫ pullback.fst y y = u ≫ m.1)
    (hv₂ : v ≫ U.ι ≫ pullback.snd y y = d) :
    ∃ w' : T ⟶ (U' y U m a ha y' ι τ : Scheme.{u}),
      w' ≫ (U' y U m a ha y' ι τ).ι = pullback.lift (u ≫ U.ι ≫ pullback.fst y y) d
        (by rw [Category.assoc, Category.assoc, hut, hd]) ≫ ch y y' ι τ ∧ w' ≫ M = v ≫ m.1 ≫ ι.1 := by
  obtain ⟨b, hb⟩ : ∃ b : T ⟶ Y, b = u ≫ U.ι ≫ pullback.fst y y := ⟨_, rfl⟩
  have hbk : b ≫ kA y a ha = u ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, kA_fst, Category.comp_id, hb, Category.assoc]
    · rw [Category.assoc, kA_snd, Category.assoc, hu, hb]
      simp only [Category.assoc]
      rw [reassoc_of% hut]
  have hbr : Set.range b.base ⊆ Set.range (Ua y U a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (kA y a ha).base (b.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, hbk, Scheme.Hom.comp_apply]
    exact (u.base z).2
  set b' : T ⟶ Ua y U a ha := IsOpenImmersion.lift (Ua y U a ha).ι b hbr
  have hb' : b' ≫ (Ua y U a ha).ι = b := IsOpenImmersion.lift_fac _ _ _
  have hbla : b' ≫ la y U a ha = u := by
    rw [← cancel_mono U.ι, Category.assoc, la_ι, reassoc_of% hb', hbk]
  set q : T ⟶ pullback y y := pullback.lift b d (by rw [hb, Category.assoc, Category.assoc, hut, hd])
  have hqr : Set.range q.base ⊆ Set.range (Ya y U a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (pullback.fst y y).base (q.base z) ∈ Ua y U a ha
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, ← hb', Scheme.Hom.comp_apply]
    exact (b'.base z).2
  set qY : T ⟶ Ya y U a ha := IsOpenImmersion.lift (Ya y U a ha).ι q hqr
  have hqY : qY ≫ (Ya y U a ha).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hqYb : qY ≫ bY y U a ha = b' := by
    rw [← cancel_mono (Ua y U a ha).ι, Category.assoc, bY_ι, reassoc_of% hqY, pullback.lift_fst, hb']
  have hqΘ : qY ≫ Θ y U m a ha = v ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, Θ_fst, reassoc_of% hqYb, rho, reassoc_of% hbla, Category.assoc, hv₁]
    · rw [Category.assoc, Θ_snd, reassoc_of% hqY, pullback.lift_snd, Category.assoc, hv₂]
  have hqVr : Set.range qY.base ⊆ Set.range (V2 y U m a ha).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (Θ y U m a ha).base (qY.base z) ∈ U
    rw [← Scheme.Hom.comp_apply, hqΘ, Scheme.Hom.comp_apply]
    exact (v.base z).2
  set qV : T ⟶ V2 y U m a ha := IsOpenImmersion.lift (V2 y U m a ha).ι qY hqVr
  have hqV : qV ≫ (V2 y U m a ha).ι = qY := IsOpenImmersion.lift_fac _ _ _
  have hqθ : qV ≫ θ y U m a ha = v := by
    rw [← cancel_mono U.ι, Category.assoc, θ_ι, reassoc_of% hqV, hqΘ]
  refine ⟨qV ≫ (eV y U m a ha).hom ≫ (e2 y U m a ha y' ι τ).hom ≫ (pullback y' y').homOfLE (P2_le y U m a ha y' ι τ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, Category.assoc, Scheme.homOfLE_ι, e2_hom_ι, eV_hom_ι_assoc,
      reassoc_of% hqV, reassoc_of% hqY]
    subst hb; rfl
  · rw [Category.assoc, Category.assoc, Category.assoc, hM2, f2, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
      reassoc_of% hqθ]

variable (M' : SchemeHomOver ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y') y') (hM' : M'.1 = M)

theorem res_fac (P : (pullback y' y').Opens) (hP : P ≤ U' y U m a ha y' ι τ) :
    ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P).ι = ((U' y U m a ha y' ι τ).ι ∣_ P) ≫ (pullback y' y').homOfLE hP := by
  rw [← cancel_mono (U' y U m a ha y' ι τ).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

def cov : Option Bool → (U' y U m a ha y' ι τ : Scheme.{u}).Opens
  | some true => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι
  | some false => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ
  | none => (U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ

theorem iSup_eq_top : (⨆ i, cov y U m a ha y' ι τ i) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  rw [Opens.mem_iSup]
  rcases hx with (hx | hx) | hx
  · exact ⟨some true, hx⟩
  · exact ⟨some false, hx⟩
  · exact ⟨none, hx⟩

include hM0 hM1 hM2 hM' in

theorem locallyQuasiFinite_Phi' [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)] :
    LocallyQuasiFinite (pullback.lift (f := y') (g := y') ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y') M'.1
      ((Category.assoc _ _ _).trans M'.2.symm)) := by
  set Φ' := pullback.lift (f := y') (g := y') ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y') M'.1
      ((Category.assoc _ _ _).trans M'.2.symm)
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ (iSup_eq_top y U m a ha y' ι τ) ?_
  rintro (_ | _ | _)
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Φ')
    haveI := isOpenImmersion_Θ y U m a ha

    haveI hθ : IsOpenImmersion (θ y U m a ha) := inferInstanceAs (IsOpenImmersion (Θ y U m a ha ∣_ U))
    obtain ⟨φ₂, hφ₁, hφ₂⟩ : ∃ φ₂ : (V2 y U m a ha : Scheme.{u}) ⟶ pullback y y,
        φ₂ ≫ pullback.fst y y = (V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y ∧
        φ₂ ≫ pullback.snd y y = θ y U m a ha ≫ m.1 :=
      ⟨pullback.lift ((V2 y U m a ha).ι ≫ (Ya y U a ha).ι ≫ pullback.fst y y) (θ y U m a ha ≫ m.1)
        (by simp only [Category.assoc]; rw [m.2, θ_ι_assoc, Θ_fst_y]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hφr : Set.range φ₂.base ⊆ Set.range (Ya y U a ha).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change (pullback.fst y y).base (φ₂.base z) ∈ Ua y U a ha
      rw [← Scheme.Hom.comp_apply, hφ₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ((V2 y U m a ha).ι.base z).2
    let φ₂' : (V2 y U m a ha : Scheme.{u}) ⟶ Ya y U a ha := IsOpenImmersion.lift (Ya y U a ha).ι φ₂ hφr
    have hφ₂' : φ₂' ≫ (Ya y U a ha).ι = φ₂ := IsOpenImmersion.lift_fac _ _ _
    have hφb : φ₂' ≫ bY y U a ha = (V2 y U m a ha).ι ≫ bY y U a ha := by
      rw [← cancel_mono (Ua y U a ha).ι, Category.assoc, Category.assoc, bY_ι, reassoc_of% hφ₂', hφ₁]
    have hφΘ : φ₂' ≫ Θ y U m a ha = θ y U m a ha ≫ Phi y U m := by
      apply pullback.hom_ext
      · rw [Category.assoc, Θ_fst, reassoc_of% hφb, Category.assoc, pullback.lift_fst, θ_ι_assoc, Θ_fst]
      · rw [Category.assoc, Θ_snd, reassoc_of% hφ₂', hφ₂, Category.assoc, pullback.lift_snd]
    haveI : LocallyQuasiFinite (θ y U m a ha ≫ Phi y U m) := inferInstance
    haveI : LocallyQuasiFinite (φ₂' ≫ Θ y U m a ha) := by rw [hφΘ]; infer_instance
    haveI : LocallyQuasiFinite φ₂' := LocallyQuasiFinite.of_comp φ₂' (Θ y U m a ha)
    haveI : LocallyQuasiFinite φ₂ := by rw [← hφ₂']; infer_instance
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m a ha).inv ≫ φ₂ ≫ ch y y' ι ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, reassoc_of% hφ₁]
        rw [← e2_inv_ι_assoc, ch_fst, ← eV_inv_ι_assoc]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι τ), Category.assoc,
          hM', hM2, f2]
        simp only [Category.assoc, ch_snd, reassoc_of% hφ₂]
    rw [h]; infer_instance
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Φ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P1 y U y' ι τ) ≫ (e1 y U y' ι τ).inv ≫ Phi y U m ≫ ch y y' τ τ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
        rw [← e1_inv_ι_assoc, ch_fst]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι τ), Category.assoc,
          hM', hM1, f1]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
    rw [h]; infer_instance
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Φ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Φ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P0 y U y' ι) ≫ (e0 y U y' ι).inv ≫ Phi y U m ≫ ch y y' ι ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, reassoc_of% (res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
        rw [← e0_inv_ι_assoc, ch_fst]
      · rw [Category.assoc, pullback.lift_snd, res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι τ), Category.assoc,
          hM', hM0, f0]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
    rw [h]; infer_instance

include hM0 hM1 hM2 hM' in

theorem locallyQuasiFinite_Psi' [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)] :
    LocallyQuasiFinite (pullback.lift (f := y') (g := y') M'.1 ((U' y U m a ha y' ι τ).ι ≫ pullback.snd y' y')
      (M'.2.trans (by rw [Category.assoc, pullback.condition]))) := by
  set Ψ' := pullback.lift (f := y') (g := y') M'.1 ((U' y U m a ha y' ι τ).ι ≫ pullback.snd y' y')
      (M'.2.trans (by rw [Category.assoc, pullback.condition]))
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ (iSup_eq_top y U m a ha y' ι τ) ?_
  rintro (_ | _ | _)
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Ψ')
    haveI := isOpenImmersion_Θ y U m a ha
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P2 y U m a ha y' ι τ).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P2 y U m a ha y' ι τ) ≫ (e2 y U m a ha y' ι τ).inv ≫ (eV y U m a ha).inv ≫
          θ y U m a ha ≫ Psi y U m ≫ ch y y' ι τ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι τ), Category.assoc,
          hM', hM2, f2]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P2_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e2_inv_ι_assoc, ch_snd, ← eV_inv_ι_assoc, θ_ι_assoc, Θ_snd_assoc]
    haveI hθ : IsOpenImmersion (θ y U m a ha) := inferInstanceAs (IsOpenImmersion (Θ y U m a ha ∣_ U))
    rw [h]; infer_instance
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Ψ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P1 y U y' ι τ).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P1 y U y' ι τ) ≫ (e1 y U y' ι τ).inv ≫ Psi y U m ≫ ch y y' τ ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι τ), Category.assoc,
          hM', hM1, f1]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P1_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e1_inv_ι_assoc, ch_snd]
    rw [h]; infer_instance
  ·
    change LocallyQuasiFinite (((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Ψ')
    have h : ((U' y U m a ha y' ι τ).ι ⁻¹ᵁ P0 y U y' ι).ι ≫ Ψ' =
        ((U' y U m a ha y' ι τ).ι ∣_ P0 y U y' ι) ≫ (e0 y U y' ι).inv ≫ Psi y U m ≫ ch y y' ι ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι τ), Category.assoc,
          hM', hM0, f0]
        simp only [Category.assoc, ch_fst, pullback.lift_fst_assoc]
      · rw [Category.assoc, pullback.lift_snd, reassoc_of% (res_fac y U m a ha y' ι τ _ (P0_le y U m a ha y' ι τ)),
          Scheme.homOfLE_ι_assoc]
        simp only [Category.assoc, ch_snd, pullback.lift_snd_assoc]
        rw [← e0_inv_ι_assoc, ch_snd]
    rw [h]; infer_instance

end Clauses

end P2mLaw535G
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.P2mLaw535G"

open P2mLaw535G in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (hΓa : pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y ≫ τ.1 =
          pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y ≫ ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ τ.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ τ.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : SchemeHomOver t y)
          (u v : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ U.ι ≫ pullback.snd y y = t ≫ a →
        v.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → v.1 ≫ U.ι ≫ pullback.snd y y = d.1 →
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = d.1 ≫ τ.1 ∧
          w'.1 ≫ m'.1 = v.1 ≫ m.1 ≫ ι.1) := by
  haveI := hΦ
  haveI := hΨ

  haveI : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫ y)
  have hgr : Set.range (grm y U m).base ⊆ Set.range γ.base := hΓ ▸ subset_closure
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hgr
  have htr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ Y) (_ : x ≫ y = t)
      (w : T ⟶ (U : Scheme.{u})),
      w ≫ U.ι ≫ pullback.fst y y = t ≫ a → w ≫ U.ι ≫ pullback.snd y y = x → x ≫ τ.1 = w ≫ m.1 ≫ ι.1 :=
    fun t x hx w hw₁ hw₂ => translate y U m a ha γ g₀ hg₀ ι τ hΓa t x hx w hw₁ hw₂

  obtain ⟨M, hM0, hM1, hM2, hMy⟩ := exists_law y U m a ha y' ι τ hU₁ hassoc htr hιd
  let m' : SchemeHomOver ((U' y U m a ha y' ι τ).ι ≫ pullback.fst y' y' ≫ y') y' := ⟨M, hMy⟩
  refine ⟨U' y U m a ha y' ι τ, m', locallyQuasiFinite_Phi' y U m a ha y' ι τ M hM0 hM1 hM2 m' rfl,
    locallyQuasiFinite_Psi' y U m a ha y' ι τ M hM0 hM1 hM2 m' rfl, ?_, ?_, ?_⟩
  · intro T t w
    obtain ⟨w', hw', hw'M⟩ := clause0 y U m a ha y' ι τ M hM0 w.1
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, ι.2, w.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd]
  · intro T t w
    obtain ⟨w', hw', hw'M⟩ := clause1 y U m a ha y' ι τ M hM1 w.1
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, τ.2, w.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd]
  · intro T t d u v hu hv₁ hv₂
    obtain ⟨w', hw', hw'M⟩ := clause2 y U m a ha y' ι τ M hM2 t d.1 d.2 u.1 v.1 u.2 hu hv₁ hv₂
    refine ⟨⟨w', ?_⟩, ?_, ?_, hw'M⟩
    · rw [reassoc_of% hw', ch_fst_assoc, ι.2, pullback.lift_fst_assoc, Category.assoc, Category.assoc, u.2]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc]
    · change w' ≫ _ = _; rw [reassoc_of% hw', ch_snd, pullback.lift_snd_assoc]

end
end S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section (solution)
