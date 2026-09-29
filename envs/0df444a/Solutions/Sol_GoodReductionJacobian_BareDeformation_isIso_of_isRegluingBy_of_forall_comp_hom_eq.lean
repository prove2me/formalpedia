-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.isIso_of_isRegluingBy_of_forall_comp_hom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bbd839cd-376a-51c1-8373-73ca3cc0de1b

import Mathlib
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_forall_comp_hom_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GlueAux

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}

theorem surjective_specMap (hπ : Function.Surjective (algebraMap B B₁))
    (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
  have hk : RingHom.ker (algebraMap B B₁) ≤ nilradical B := by
    intro x hx
    obtain ⟨n, hn⟩ := hker
    rw [mem_nilradical]
    exact ⟨n, by simpa [hn, Submodule.zero_eq_bot, Submodule.mem_bot] using Ideal.pow_mem_pow hx n⟩
  have H : ∀ x : B₁, ∃ n > 0, x ^ n ∈ (algebraMap B B₁).range := fun x => by
    obtain ⟨b, hb⟩ := hπ x
    exact ⟨1, one_pos, b, by rw [pow_one, hb]⟩
  have hs := (PrimeSpectrum.isHomeomorph_comap (algebraMap B B₁) H hk).surjective
  refine ⟨fun x => ?_⟩
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  rw [Spec.map_apply]
  exact hy

theorem g_bijective (hπ : Function.Surjective (algebraMap B B₁))
    (hker : IsNilpotent (RingHom.ker (algebraMap B B₁))) (D : BareDeformation f₁ L₁ B) :
    Function.Surjective D.g ∧ Function.Injective D.g := by
  have hS := surjective_specMap hπ hker
  have hC : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have h1 : Surjective D.g := MorphismProperty.of_isPullback D.cart.flip hS
  have h2 : IsClosedImmersion D.g := MorphismProperty.of_isPullback D.cart.flip hC
  exact ⟨D.g.surjective, D.g.isClosedEmbedding.injective⟩

theorem glue_hom (hπ : Function.Surjective (algebraMap B B₁))
    (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (D₀ D D' : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s)))
    (ι : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A) (hιopen : ∀ i, IsOpenImmersion (ι i))
    (hιsurj : ∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ι i).base y = x)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ι i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0) = τ s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1))
    (ι' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D'.A)
    (hιglue' : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι' (s.1 0) = τ' s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1))
    (α : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ ↑(𝒰.U i))
    (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s))
    (hαr : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      αr s j ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ α (s.1 j))
    (hcomm : ∀ s : 𝒰.Idx 1, αr s 0 ≫ τ' s = τ s ≫ αr s 1) :
    ∃ e : D.A ⟶ D'.A, ∀ i, ι i ≫ e = α i ≫ ι' i := by
  classical
  haveI : ∀ i, IsOpenImmersion (ι i) := hιopen
  obtain ⟨hg₀s, -⟩ := g_bijective hπ hker D₀
  obtain ⟨-, hgi⟩ := g_bijective hπ hker D

  have inter_ge : ∀ s : 𝒰.Idx 1, 𝒰.U (s.1 0) ⊓ 𝒰.U (s.1 1) ≤ 𝒰.inter s := fun s => by
    change _ ≤ ⨅ j, 𝒰.U (s.1 j)
    exact le_iInf (Fin.forall_fin_two.2 ⟨inf_le_left, inf_le_right⟩)

  have key : ∀ (i : 𝒰.ι) (y : ↑(𝒰.U i)) (x : A₁), D₀.g x = (𝒰.U i).ι y → ι i y = D.g x := by
    intro i y x hx
    have hx' : x ∈ D₀.g ⁻¹ᵁ 𝒰.U i := by
      show D₀.g x ∈ 𝒰.U i
      rw [hx]
      exact y.2
    have h1 : (D₀.g ∣_ 𝒰.U i) ⟨x, hx'⟩ = y :=
      Subtype.ext (by rw [morphismRestrict_base_coe]; exact hx)
    calc ι i y = ((D₀.g ∣_ 𝒰.U i) ≫ ι i) ⟨x, hx'⟩ := by rw [Scheme.Hom.comp_apply, h1]
      _ = ((D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g) ⟨x, hx'⟩ := by rw [hιg]
      _ = D.g x := by rw [Scheme.Hom.comp_apply]; rfl

  have hrange : ∀ s : 𝒰.Idx 1, Set.range (pullback.fst (ι (s.1 0)) (ι (s.1 1))) ⊆
      Set.range (D₀.A.homOfLE (𝒰.inter_le s 0)) := by
    intro s
    rw [Scheme.Pullback.range_fst]
    rintro y ⟨y', hy'⟩
    obtain ⟨x, hx⟩ := hg₀s ((𝒰.U (s.1 0)).ι y)
    obtain ⟨x', hx'⟩ := hg₀s ((𝒰.U (s.1 1)).ι y')
    have e1 := key _ y x hx
    have e2 := key _ y' x' hx'
    have hxx : x = x' := hgi (by rw [← e1, ← e2]; exact hy'.symm)
    subst hxx
    have hmem : (𝒰.U (s.1 0)).ι y ∈ 𝒰.inter s :=
      inter_ge s ⟨y.2, by rw [← hx, hx']; exact y'.2⟩
    exact ⟨⟨_, hmem⟩, Subtype.ext (by rw [Scheme.homOfLE_apply]; rfl)⟩

  have compat_s : ∀ s : 𝒰.Idx 1,
      pullback.fst (ι (s.1 0)) (ι (s.1 1)) ≫ α (s.1 0) ≫ ι' (s.1 0) =
        pullback.snd (ι (s.1 0)) (ι (s.1 1)) ≫ α (s.1 1) ≫ ι' (s.1 1) := by
    intro s
    obtain ⟨φ, hφ⟩ : ∃ φ : pullback (ι (s.1 0)) (ι (s.1 1)) ⟶ ↑(𝒰.inter s),
        φ ≫ D₀.A.homOfLE (𝒰.inter_le s 0) = pullback.fst (ι (s.1 0)) (ι (s.1 1)) :=
      ⟨_, IsOpenImmersion.lift_fac _ _ (hrange s)⟩
    have hφ' : φ ≫ τ s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) = pullback.snd (ι (s.1 0)) (ι (s.1 1)) := by
      rw [← cancel_mono (ι (s.1 1)), Category.assoc, Category.assoc, ← hιglue s, ← Category.assoc, hφ,
        pullback.condition]
    have hc : D₀.A.homOfLE (𝒰.inter_le s 0) ≫ α (s.1 0) ≫ ι' (s.1 0) =
        τ s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ α (s.1 1) ≫ ι' (s.1 1) :=
      calc D₀.A.homOfLE (𝒰.inter_le s 0) ≫ α (s.1 0) ≫ ι' (s.1 0)
          = αr s 0 ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι' (s.1 0) := by rw [reassoc_of% (hαr s 0)]
        _ = αr s 0 ≫ τ' s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1) := by rw [hιglue' s]
        _ = τ s ≫ αr s 1 ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1) := by rw [reassoc_of% (hcomm s)]
        _ = τ s ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ α (s.1 1) ≫ ι' (s.1 1) := by
          rw [reassoc_of% (hαr s 1)]
    rw [← hφ, ← hφ']
    simp only [Category.assoc]
    rw [hc]

  have compat : ∀ i j : 𝒰.ι,
      pullback.fst (ι i) (ι j) ≫ α i ≫ ι' i = pullback.snd (ι i) (ι j) ≫ α j ≫ ι' j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · exact compat_s ⟨![i, j], by simp [h]⟩
    · rw [fst_eq_snd_of_mono_eq]
    · have := compat_s ⟨![j, i], by simp [h]⟩
      rw [← cancel_epi (pullbackSymmetry (ι j) (ι i)).hom, pullbackSymmetry_hom_comp_fst_assoc,
        pullbackSymmetry_hom_comp_snd_assoc]
      exact this.symm

  let 𝒱 : D.A.OpenCover :=
    Scheme.Cover.mkOfCovers 𝒰.ι (fun i => (↑(𝒰.U i) : Scheme.{0})) ι hιsurj hιopen
  exact ⟨Scheme.Cover.glueMorphisms 𝒱 (fun i => α i ≫ ι' i) compat,
    fun i => Scheme.Cover.ι_glueMorphisms 𝒱 (fun i => α i ≫ ι' i) compat i⟩

end GlueAux

theorem solution
    {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ D D' : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D')
    (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
    (hαf : ∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hαg : ∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i)
    (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hαr : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom)
    (hcomm : ∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) :
    D.IsIso D' := by
  obtain ⟨-, -, ι, hιopen, hιf, hιsurj, hιg, hιglue⟩ := hD
  obtain ⟨-, -, ι', hιopen', hιf', hιsurj', hιg', hιglue'⟩ := hD'
  obtain ⟨e₁, he₁⟩ := GlueAux.glue_hom hπ hker D₀ D D' 𝒰 (fun s => (τ s).hom) (fun s => (τ' s).hom)
    ι hιopen hιsurj hιg hιglue ι' hιglue' (fun i => (α i).hom) (fun s j => (αr s j).hom) hαr hcomm
  have hαr' : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      (αr s j).inv ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).inv := by
    intro s j
    rw [Iso.inv_comp_eq, reassoc_of% (hαr s j), Iso.hom_inv_id, Category.comp_id]
  have hcomm' : ∀ s : 𝒰.Idx 1, (αr s 0).inv ≫ (τ s).hom = (τ' s).hom ≫ (αr s 1).inv := by
    intro s
    rw [Iso.inv_comp_eq, reassoc_of% (hcomm s), Iso.hom_inv_id, Category.comp_id]
  obtain ⟨e₂, he₂⟩ := GlueAux.glue_hom hπ hker D₀ D' D 𝒰 (fun s => (τ' s).hom) (fun s => (τ s).hom)
    ι' hιopen' hιsurj' hιg' hιglue' ι hιglue (fun i => (α i).inv) (fun s j => (αr s j).inv) hαr' hcomm'
  haveI : ∀ i, IsOpenImmersion (ι i) := hιopen
  haveI : ∀ i, IsOpenImmersion (ι' i) := hιopen'
  let 𝒱 : D.A.OpenCover :=
    Scheme.Cover.mkOfCovers 𝒰.ι (fun i => (↑(𝒰.U i) : Scheme.{0})) ι hιsurj hιopen
  let 𝒱' : D'.A.OpenCover :=
    Scheme.Cover.mkOfCovers 𝒰.ι (fun i => (↑(𝒰.U i) : Scheme.{0})) ι' hιsurj' hιopen'
  have h12 : e₁ ≫ e₂ = 𝟙 D.A := Scheme.Cover.hom_ext 𝒱 _ _ fun i => by
    show ι i ≫ e₁ ≫ e₂ = ι i ≫ 𝟙 D.A
    rw [reassoc_of% (he₁ i), he₂ i, Iso.hom_inv_id_assoc, Category.comp_id]
  have h21 : e₂ ≫ e₁ = 𝟙 D'.A := Scheme.Cover.hom_ext 𝒱' _ _ fun i => by
    show ι' i ≫ e₂ ≫ e₁ = ι' i ≫ 𝟙 D'.A
    rw [reassoc_of% (he₂ i), he₁ i, Iso.inv_hom_id_assoc, Category.comp_id]
  show ∃ e : D.A ≅ D'.A, e.hom ≫ D'.f = D.f ∧ D.g ≫ e.hom = D'.g
  refine ⟨⟨e₁, e₂, h12, h21⟩, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒱 _ _ fun i => ?_
    show ι i ≫ e₁ ≫ D'.f = ι i ≫ D.f
    rw [reassoc_of% (he₁ i), hιf' i, hαf i, hιf i]
  · refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨i, hi⟩ : ∃ i, D₀.g x ∈ 𝒰.U i := by
      have hx : D₀.g x ∈ ⨆ i, 𝒰.U i := by
        rw [𝒰.iSup_eq_top]
        exact TopologicalSpace.Opens.mem_top _
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨D₀.g ⁻¹ᵁ 𝒰.U i, hi, ?_⟩
    show (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g ≫ e₁ = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D'.g
    rw [← reassoc_of% (hιg i), he₁ i, reassoc_of% (hαg i), hιg' i]

end S_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_forall_comp_hom_eq
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_isIso_of_isRegluingBy_of_forall_comp_hom_eq (solution)
