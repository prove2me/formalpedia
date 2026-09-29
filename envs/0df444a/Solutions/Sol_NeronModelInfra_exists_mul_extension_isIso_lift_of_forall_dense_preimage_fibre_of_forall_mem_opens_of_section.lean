-- Prove2me | solution 1 for NeronModelInfra.exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d36d69aa-9813-50a4-bc42-380f145e7dc7

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace P2mGExt

section FibreMax

def FibMax {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∀ x' : X, x' ⤳ x → f.base x' = f.base x → x' = x

theorem fibMax_of_maximal {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} (h : ∀ x' : X, x' ⤳ x → x' = x) :
    FibMax f x := fun x' h' _ => h x' h'

theorem maximal_of_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap f.base) {x : X}
    (h : ∀ x' : X, x' ⤳ x → x' = x) : ∀ y' : Y, y' ⤳ f.base x → y' = f.base x := by
  intro y' hy'
  obtain ⟨x', hx', rfl⟩ := hf hy'
  rw [h x' hx']

theorem fibMax_comp_of_injective {A B C : Scheme.{u}} (e : A ⟶ B) (β : B ⟶ C) (he : Function.Injective e.base)
    {q : A} (h : FibMax β (e.base q)) : FibMax (e ≫ β) q := by
  intro q' hq' hf
  apply he
  refine h _ (hq'.map e.continuous) ?_
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using hf

theorem fibMax_of_isOpenImmersion {A B C : Scheme.{u}} (e : A ⟶ B) [IsOpenImmersion e] (β : B ⟶ C)
    {q : A} (h : FibMax (e ≫ β) q) : FibMax β (e.base q) := by
  intro x' hx' hf
  have hx'r : x' ∈ Set.range e.base := hx'.mem_open e.isOpenEmbedding.isOpen_range ⟨q, rfl⟩
  obtain ⟨q', rfl⟩ := hx'r
  have hq' : q' ⤳ q := (e.isOpenEmbedding.isEmbedding.isInducing.specializes_iff).mp hx'
  rw [h q' hq' (by simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using hf)]

theorem maximal_of_dominated {A B B'' : Scheme.{u}} (G : A ⟶ B) (H : B'' ⟶ A) (π : B'' ⟶ B)
    (hπ : GeneralizingMap π.base) (hGH : H ≫ G = π) {b : B''} {x : A} (hx : H.base b = x)
    (h : ∀ x' : A, x' ⤳ x → x' = x) : ∀ y' : B, y' ⤳ G.base x → y' = G.base x := by
  intro y' hy'
  have hGx : G.base x = π.base b := by rw [← hx, ← Scheme.Hom.comp_apply, hGH]
  rw [hGx] at hy' ⊢
  obtain ⟨b', hb', rfl⟩ := hπ hy'
  have h1 : H.base b' ⤳ x := hx ▸ hb'.map H.continuous
  have h2 : H.base b' = x := h _ h1
  rw [← hGH, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2, hx]

theorem fibMax_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) {ω : P} (hω : FibMax snd ω) : FibMax f (fst.base ω) := by

  obtain ⟨φ, hφflat, hφι⟩ : ∃ φ : snd.fiber (snd.base ω) ⟶ f.fiber (g.base (snd.base ω)),
      Flat φ ∧ φ ≫ f.fiberι (g.base (snd.base ω)) = snd.fiberι (snd.base ω) ≫ fst := by
    haveI : Flat (Spec.map (g.residueFieldMap (snd.base ω))) := by
      haveI : Subsingleton ↥(Spec (Z.residueField (g.base (snd.base ω)))) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum (Z.residueField (g.base (snd.base ω)))))
      infer_instance
    exact ⟨_, MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback h (snd.base ω)).flip
      inferInstance, pullback.lift_fst _ _ _⟩
  haveI := hφflat
  have hgen : GeneralizingMap φ.base := Flat.generalizingMap φ

  let ξ : ↥(snd.fiber (snd.base ω)) := snd.asFiber ω
  have hξ : (snd.fiberι (snd.base ω)).base ξ = ω := snd.fiberι_asFiber ω
  have hfstω : (f.fiberι (g.base (snd.base ω))).base (φ.base ξ) = fst.base ω := by
    have := congrArg (fun k => k.base ξ) hφι
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply, hξ] using this
  intro x' hx' hfx'
  have hfω : f.base (fst.base ω) = g.base (snd.base ω) := by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have hx'mem : x' ∈ Set.range (f.fiberι (g.base (snd.base ω))).base := by
    rw [Scheme.Hom.range_fiberι]; simpa [hfω] using hfx'
  obtain ⟨χ, rfl⟩ := hx'mem
  rw [← hfstω] at hx' ⊢
  have hχ : χ ⤳ φ.base ξ :=
    ((f.fiberι (g.base (snd.base ω))).isEmbedding.isInducing.specializes_iff).mp hx'
  obtain ⟨ξ', hξ', hξ'χ⟩ := hgen hχ
  have h1 : (snd.fiberι (snd.base ω)).base ξ' ⤳ ω := by
    have := hξ'.map (snd.fiberι (snd.base ω)).continuous
    rwa [hξ] at this
  have h2 : snd.base ((snd.fiberι (snd.base ω)).base ξ') = snd.base ω := by
    have : (snd.fiberι (snd.base ω)).base ξ' ∈ snd.base ⁻¹' {snd.base ω} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨ξ', rfl⟩
    simpa using this
  have h3 : (snd.fiberι (snd.base ω)).base ξ' = (snd.fiberι (snd.base ω)).base ξ := (hω _ h1 h2).trans hξ.symm
  have h4 : ξ' = ξ := (snd.fiberι (snd.base ω)).isEmbedding.injective h3
  rw [← hξ'χ, h4]

theorem exists_fibMax {X Y : Scheme.{u}} (f : X ⟶ Y) (t : Y) (ht : t ∈ Set.range f.base) :
    ∃ ω : X, f.base ω = t ∧ FibMax f ω := by
  have hne : Nonempty ↥(f.fiber t) := by
    obtain ⟨x, hx⟩ := ht
    have : x ∈ Set.range (f.fiberι t).base := by rw [Scheme.Hom.range_fiberι]; simpa using hx
    obtain ⟨ξ, _⟩ := this
    exact ⟨ξ⟩
  obtain ⟨ξ₀⟩ := hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := ξ₀)) isClosed_irreducibleComponent
  have hξmax : ∀ x' : ↥(f.fiber t), x' ⤳ ξ → x' = ξ := by
    intro x' hx'
    have h1 : irreducibleComponent ξ₀ ⊆ closure {x'} := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hx')) isClosed_closure
    have h2 : closure {x'} = irreducibleComponent ξ₀ :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
    exact IsGenericPoint.eq (isGenericPoint_def.mpr h2) hξ
  refine ⟨(f.fiberι t).base ξ, ?_, ?_⟩
  · have : (f.fiberι t).base ξ ∈ f.base ⁻¹' {t} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨ξ, rfl⟩
    simpa using this
  · intro ω' hω' hfω'
    have hmem : ω' ∈ Set.range (f.fiberι t).base := by
      rw [Scheme.Hom.range_fiberι]
      have : (f.fiberι t).base ξ ∈ f.base ⁻¹' {t} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨ξ, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
      rw [hfω', this]
    obtain ⟨ξ', rfl⟩ := hmem
    rw [hξmax ξ' (((f.fiberι t).isEmbedding.isInducing.specializes_iff).mp hω')]

theorem mem_of_dense_of_maximal {T : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace.NoetherianSpace T] {O : Set T} (hO : Dense O) (hO' : IsOpen O) {ξ : T}
    (hξ : ∀ x : T, x ⤳ ξ → x = ξ) : ξ ∈ O := by
  classical
  let F : Set (Set T) := {C ∈ irreducibleComponents T | ξ ∉ C}
  have hFfin : F.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun C hC => hC.1)
  let N : Set T := (⋃₀ F)ᶜ
  have hN : IsOpen N := by
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hFfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hξN : ξ ∈ N := fun ⟨C, hC, hξC⟩ => hC.2 hξC
  have hNsub : N ⊆ closure {ξ} := by
    intro p hp
    have hC := irreducibleComponent_mem_irreducibleComponents p
    have hξC : ξ ∈ irreducibleComponent p := by
      by_contra hcon
      exact hp (Set.mem_sUnion.mpr ⟨_, ⟨hC, hcon⟩, mem_irreducibleComponent⟩)
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := p)) isClosed_irreducibleComponent
    have hηξ : η ⤳ ξ := hη.specializes hξC
    have := hξ η hηξ
    subst this
    rw [hη.def]
    exact mem_irreducibleComponent
  obtain ⟨p, hpN, hpO⟩ := hO.inter_open_nonempty N hN ⟨ξ, hξN⟩
  exact (specializes_iff_mem_closure.mpr (hNsub hpN)).mem_open hO' hpO

theorem mem_of_dense_fibre_of_fibMax {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (S : X.Opens)
    (x₀ : Y) (hd : Dense ((Subtype.val : {q : X // f.base q = x₀} → X) ⁻¹' (S : Set X)))
    {q : X} (hq : f.base q = x₀) (hmax : FibMax f q) : q ∈ S := by

  let F : Scheme.{u} := f.fiber x₀
  let ι : F ⟶ X := f.fiberι x₀
  haveI : IsLocallyNoetherian F := by
    change IsLocallyNoetherian (pullback f (Y.fromSpecResidueField x₀)); infer_instance
  have hrange : Set.range ι.base = f.base ⁻¹' {x₀} := Scheme.Hom.range_fiberι f x₀
  obtain ⟨ξ, hξ⟩ : q ∈ Set.range ι.base := by rw [hrange]; simpa using hq

  have hξmax : ∀ x : F, x ⤳ ξ → x = ξ := by
    intro x hx
    apply ι.isEmbedding.injective
    rw [hξ]
    refine hmax _ (hξ ▸ hx.map ι.continuous) ?_
    have : ι.base x ∈ f.base ⁻¹' {x₀} := hrange ▸ ⟨x, rfl⟩
    rw [hq]; simpa using this

  have hO : Dense ((ι ⁻¹ᵁ S : F.Opens) : Set F) := by
    rw [ι.isEmbedding.isInducing.dense_iff]
    intro x
    have hx : ι.base x ∈ f.base ⁻¹' {x₀} := hrange ▸ ⟨x, rfl⟩
    have h1 := (IsInducing.subtypeVal.dense_iff).mp hd ⟨ι.base x, by simp at hx; exact hx⟩
    refine closure_mono ?_ h1
    rintro _ ⟨⟨z, hz⟩, hzS, rfl⟩
    obtain ⟨w, rfl⟩ : z ∈ Set.range ι.base := by rw [hrange]; (simp at hz; exact hz)
    exact ⟨w, hzS, rfl⟩

  obtain ⟨_, ⟨A, hA, rfl⟩, hξA, -⟩ := F.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
  haveI : IsNoetherianRing Γ(F, A) := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  haveI : TopologicalSpace.NoetherianSpace ↥A := noetherianSpace_of_isAffineOpen A hA
  have hOA : Dense ((Scheme.Opens.ι A).base ⁻¹' ((ι ⁻¹ᵁ S : F.Opens) : Set F)) :=
    hO.preimage (Scheme.Opens.ι A).isOpenEmbedding.isOpenMap
  have hξ' : ∀ x : ↥A, x ⤳ (⟨ξ, hξA⟩ : ↥A) → x = ⟨ξ, hξA⟩ := by
    intro x hx
    apply Subtype.ext
    exact hξmax _ (hx.map continuous_subtype_val)
  haveI : TopologicalSpace.NoetherianSpace ↥((A : F.Opens) : Scheme.{u}) := this
  have key := mem_of_dense_of_maximal (T := ↥((A : F.Opens) : Scheme.{u})) hOA
    ((ι ⁻¹ᵁ S).isOpen.preimage (Scheme.Opens.ι A).continuous) hξ'
  change ι.base ((Scheme.Opens.ι A).base ⟨ξ, hξA⟩) ∈ S at key
  rwa [Scheme.Opens.ι_apply, hξ] at key

theorem dense_of_forall_dense_fibre {X Y : Scheme.{u}} (f : X ⟶ Y) (S : Set X)
    (h : ∀ x : Y, Dense ((Subtype.val : {q : X // f.base q = x} → X) ⁻¹' S)) : Dense S := by
  intro q
  have := (IsInducing.subtypeVal.dense_iff).mp (h (f.base q)) ⟨q, rfl⟩
  exact closure_mono (Set.image_preimage_subset _ _) this

theorem dense_of_forall_maximal_mem {X : Scheme.{u}} {S : Set X}
    (h : ∀ x : X, (∀ x' : X, x' ⤳ x → x' = x) → x ∈ S) : Dense S := by
  intro x
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have hξx : ξ ⤳ x := hξ.specializes mem_irreducibleComponent
  have hξmax : ∀ x' : X, x' ⤳ ξ → x' = ξ := by
    intro x' hx'
    have h1 : irreducibleComponent x ⊆ closure {x'} := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hx')) isClosed_closure
    have h2 : closure {x'} = irreducibleComponent x :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
    exact IsGenericPoint.eq (isGenericPoint_def.mpr h2) hξ
  exact hξx.mem_closed isClosed_closure (subset_closure (h ξ hξmax))

theorem maximal_of_injective {A B : Scheme.{u}} (e : A ⟶ B) (he : Function.Injective e.base) {q : A}
    (h : ∀ x' : B, x' ⤳ e.base q → x' = e.base q) (q' : A) (hq' : q' ⤳ q) : q' = q :=
  he (h _ (hq'.map e.continuous))

end FibreMax

section Descent

theorem exists_extension_of_descent {S Z Z' Yt : Scheme.{u}} (s : Z ⟶ S) (yS : Yt ⟶ S) [IsSeparated yS]
    [IsReduced Z] (V : Z.Opens) (f : (V : Scheme.{u}) ⟶ Yt) (hf : f ≫ yS = V.ι ≫ s)
    (p : Z' ⟶ Z) [Flat p] [LocallyOfFinitePresentation p] [Surjective p] [IsReduced (pullback p p)]
    (f' : Z' ⟶ Yt) (hf' : f' ≫ yS = p ≫ s)
    (Ω : Z'.Opens) (hΩ : Dense (Ω : Set Z')) (hΩV : Ω ≤ p ⁻¹ᵁ V)
    (hagree : Ω.ι ≫ f' = p.resLE V Ω hΩV ≫ f) :
    ∃ F : Z ⟶ Yt, p ≫ F = f' ∧ V.ι ≫ F = f ∧ F ≫ yS = s := by

  have key : pullback.fst p p ≫ f' = pullback.snd p p ≫ f' := by
    let Ω₂ : (pullback p p).Opens := pullback.fst p p ⁻¹ᵁ Ω ⊓ pullback.snd p p ⁻¹ᵁ Ω
    haveI : IsDominant Ω₂.ι := by
      refine ⟨?_⟩
      rw [DenseRange, Scheme.Opens.range_ι]
      simp only [Ω₂, TopologicalSpace.Opens.coe_inf]
      exact (hΩ.preimage (pullback.fst p p).isOpenMap).inter_of_isOpen_left
        (hΩ.preimage (pullback.snd p p).isOpenMap) (pullback.fst p p ⁻¹ᵁ Ω).isOpen
    refine ext_of_isDominant_of_isSeparated yS ?_ Ω₂.ι ?_
    · rw [Category.assoc, hf', Category.assoc, hf', pullback.condition_assoc]
    · let r₁ : (Ω₂ : Scheme.{u}) ⟶ Ω := (pullback.fst p p).resLE Ω Ω₂ inf_le_left
      let r₂ : (Ω₂ : Scheme.{u}) ⟶ Ω := (pullback.snd p p).resLE Ω Ω₂ inf_le_right
      have e₁ : r₁ ≫ Ω.ι = Ω₂.ι ≫ pullback.fst p p := Scheme.Hom.resLE_comp_ι _ _
      have e₂ : r₂ ≫ Ω.ι = Ω₂.ι ≫ pullback.snd p p := Scheme.Hom.resLE_comp_ι _ _
      have e₃ : r₁ ≫ p.resLE V Ω hΩV = r₂ ≫ p.resLE V Ω hΩV := by
        rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, reassoc_of% e₁,
          reassoc_of% e₂, pullback.condition]
      rw [← reassoc_of% e₁, ← reassoc_of% e₂, hagree, reassoc_of% e₃]

  have hdesc : ∀ {T : Scheme.{u}} (g₁ g₂ : T ⟶ Z'), g₁ ≫ p = g₂ ≫ p → g₁ ≫ f' = g₂ ≫ f' := by
    intro T g₁ g₂ h
    rw [← pullback.lift_fst g₁ g₂ h, Category.assoc, key, pullback.lift_snd_assoc]
  let F : Z ⟶ Yt := EffectiveEpi.desc p f' hdesc
  have hF : p ≫ F = f' := EffectiveEpi.fac p f' hdesc
  have hFs : F ≫ yS = s := by
    haveI : Epi p := inferInstance
    rw [← cancel_epi p, reassoc_of% hF, hf']
  refine ⟨F, hF, ?_, hFs⟩

  let ρ : (Ω : Scheme.{u}) ⟶ V := p.resLE V Ω hΩV
  have hρ : ρ ≫ V.ι = Ω.ι ≫ p := Scheme.Hom.resLE_comp_ι _ _
  haveI : IsDominant ρ := by
    refine ⟨?_⟩
    have hd : Dense (V.ι.base ⁻¹' (p.base '' (Ω : Set Z'))) :=
      (p.surjective.denseRange.dense_image p.continuous hΩ).preimage V.ι.isOpenMap
    rw [DenseRange]
    refine hd.mono ?_
    rintro v ⟨z, hz, hv⟩
    refine ⟨⟨z, hz⟩, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hρ, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hv]
  refine ext_of_isDominant_of_isSeparated yS ?_ ρ ?_
  · rw [Category.assoc, hFs, hf]
  · rw [reassoc_of% hρ, hF, hagree]

end Descent

structure Chunk (R : Type u) [CommRing R] where

  Y : Scheme.{u}

  P : Scheme.{u}

  y : Y ⟶ Spec (CommRingCat.of R)

  π₁ : P ⟶ Y

  π₂ : P ⟶ Y
  hP : IsPullback π₁ π₂ y y

  U : P.Opens

  m : (U : Scheme.{u}) ⟶ Y
  hm : m ≫ y = U.ι ≫ π₁ ≫ y

  Φ : (U : Scheme.{u}) ⟶ P

  Ψ : (U : Scheme.{u}) ⟶ P
  Φ_fst : Φ ≫ π₁ = U.ι ≫ π₁
  Φ_snd : Φ ≫ π₂ = m
  Ψ_fst : Ψ ≫ π₁ = m
  Ψ_snd : Ψ ≫ π₂ = U.ι ≫ π₂
  Φ_open : IsOpenImmersion Φ
  Ψ_open : IsOpenImmersion Ψ
  y_smooth : Smooth y
  y_sep : IsSeparated y
  π₁_smooth : Smooth π₁
  π₂_smooth : Smooth π₂
  π₁_surj : Surjective π₁
  π₂_surj : Surjective π₂

attribute [scoped instance] Chunk.Φ_open Chunk.Ψ_open Chunk.y_smooth Chunk.y_sep Chunk.π₁_smooth Chunk.π₂_smooth
  Chunk.π₁_surj Chunk.π₂_surj

namespace Chunk

variable {R : Type u} [CommRing R] (D : Chunk R)

attribute [reassoc] hm Φ_fst Φ_snd Ψ_fst Ψ_snd

def flip : Chunk R where
  Y := D.Y
  P := D.P
  y := D.y
  π₁ := D.π₂
  π₂ := D.π₁
  hP := D.hP.flip
  U := D.U
  m := D.m
  hm := by rw [D.hm, D.hP.w]
  Φ := D.Ψ
  Ψ := D.Φ
  Φ_fst := D.Ψ_snd
  Φ_snd := D.Ψ_fst
  Ψ_fst := D.Φ_snd
  Ψ_snd := D.Φ_fst
  Φ_open := D.Ψ_open
  Ψ_open := D.Φ_open
  y_smooth := D.y_smooth
  y_sep := D.y_sep
  π₁_smooth := D.π₂_smooth
  π₂_smooth := D.π₁_smooth
  π₁_surj := D.π₂_surj
  π₂_surj := D.π₁_surj

def Assoc : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y)),
    u.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.U.ι ≫ D.π₁ →
    p.1 ≫ D.U.ι ≫ D.π₁ = u.1 ≫ D.m → p.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.U.ι ≫ D.π₂ →
    q.1 ≫ D.U.ι ≫ D.π₁ = u.1 ≫ D.U.ι ≫ D.π₁ → q.1 ≫ D.U.ι ≫ D.π₂ = v.1 ≫ D.m →
    p.1 ≫ D.m = q.1 ≫ D.m

def FibDense (π : D.P ⟶ D.Y) (S : Set D.P) : Prop :=
  ∀ x : D.Y, Dense ((Subtype.val : {q : D.P // π.base q = x} → D.P) ⁻¹' S)

def MaxMem (Y₀ : D.Y.Opens) : Prop :=
  ∀ p : D.Y, (∀ p' : D.Y, p' ⤳ p → D.y.base p' = D.y.base p → p' = p) → p ∈ Y₀

def SqSub (Y₀ : D.Y.Opens) : Prop :=
  ∀ q : D.P, D.π₁.base q ∈ Y₀ → D.π₂.base q ∈ Y₀ → q ∈ D.U

theorem assoc_flip (h : D.Assoc) : D.flip.Assoc := by
  intro T t u v p q h1 h2 h3 h4 h5
  change _ ≫ D.m = _ ≫ D.m
  have e : D.U.ι ≫ D.π₁ ≫ D.y = D.U.ι ≫ D.π₂ ≫ D.y := by rw [D.hP.w]
  let c : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₂ ≫ D.y) → NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    fun w => ⟨w.1, by rw [e]; exact w.2⟩
  exact (h t (c v) (c u) (c q) (c p) h1.symm h5 h4 h3 h2).symm

theorem sqSub_flip {Y₀ : D.Y.Opens} (h : D.SqSub Y₀) : D.flip.SqSub Y₀ := fun q h₁ h₂ => h q h₂ h₁

theorem isReduced_P [IsDomain R] [IsDiscreteValuationRing R] : IsReduced D.P :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (D.π₁ ≫ D.y)

abbrev Y3 : Scheme.{u} := pullback D.π₂ D.π₁

abbrev P12 : D.Y3 ⟶ D.P := pullback.fst D.π₂ D.π₁

abbrev P23 : D.Y3 ⟶ D.P := pullback.snd D.π₂ D.π₁

def outer : D.Y3 ⟶ D.P :=
  D.hP.lift (D.P12 ≫ D.π₁) (D.P23 ≫ D.π₂)
    (by rw [Category.assoc, Category.assoc, D.hP.w, pullback.condition_assoc, D.hP.w])

@[reassoc (attr := simp)]
theorem outer_fst : D.outer ≫ D.π₁ = D.P12 ≫ D.π₁ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem outer_snd : D.outer ≫ D.π₂ = D.P23 ≫ D.π₂ := D.hP.lift_snd _ _ _

theorem isPullback_P12_outer : IsPullback D.P12 D.outer D.π₁ D.π₁ := by
  have s : IsPullback (D.P23 ≫ D.π₂) D.P12 D.y (D.π₁ ≫ D.y) := by
    have := (IsPullback.of_hasPullback D.π₂ D.π₁).flip.paste_horiz D.hP.flip
    rwa [← D.hP.w] at this
  have h : IsPullback D.outer D.P12 D.π₁ D.π₁ :=
    IsPullback.of_right (h₁₂ := D.π₂) (v₁₃ := D.y) (h₂₂ := D.y) (by rwa [outer_snd]) D.outer_fst D.hP.flip
  exact h.flip

theorem isPullback_P23_outer : IsPullback D.P23 D.outer D.π₂ D.π₂ := by
  have s : IsPullback (D.P12 ≫ D.π₁) D.P23 D.y (D.π₂ ≫ D.y) := by
    have := (IsPullback.of_hasPullback D.π₂ D.π₁).paste_horiz D.hP
    rwa [D.hP.w] at this
  have h : IsPullback D.outer D.P23 D.π₂ D.π₂ :=
    IsPullback.of_right (h₁₂ := D.π₁) (v₁₃ := D.y) (h₂₂ := D.y) (by rwa [outer_fst]) D.outer_snd D.hP
  exact h.flip

scoped instance smooth_outer : Smooth D.outer := MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

scoped instance surjective_outer : Surjective D.outer :=
  MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

abbrev V : D.P.Opens := D.Φ.opensRange

theorem coe_V : (D.V : Set D.P) = Set.range D.Φ.base := Scheme.Hom.coe_opensRange D.Φ

abbrev linv : (D.V : Scheme.{u}) ⟶ D.U := D.Φ.isoOpensRange.inv

@[reassoc]
theorem linv_Φ : D.linv ≫ D.Φ = D.V.ι := D.Φ.isoOpensRange_inv_comp

@[reassoc]
theorem linv_fst : D.linv ≫ D.U.ι ≫ D.π₁ = D.V.ι ≫ D.π₁ := by rw [← D.Φ_fst, linv_Φ_assoc]

@[reassoc]
theorem linv_m : D.linv ≫ D.m = D.V.ι ≫ D.π₂ := by rw [← D.Φ_snd, linv_Φ_assoc]

def divl : (D.V : Scheme.{u}) ⟶ D.Y := D.linv ≫ D.U.ι ≫ D.π₂

abbrev ZM : Scheme.{u} := pullback (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁)

def jM : D.ZM ⟶ D.Y3 :=
  pullback.map (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) D.π₂ D.π₁ D.U.ι D.V.ι (𝟙 D.Y)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)

scoped instance : IsOpenImmersion D.jM :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

@[reassoc (attr := simp)]
theorem jM_P12 : D.jM ≫ D.P12 = pullback.fst _ _ ≫ D.U.ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jM_P23 : D.jM ≫ D.P23 = pullback.snd _ _ ≫ D.V.ι := pullback.lift_snd _ _ _

def FM : D.ZM ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.m) (pullback.snd _ _ ≫ D.divl)
    (by
      rw [Category.assoc, D.hm, Category.assoc, D.hP.w,
        reassoc_of% (pullback.condition (f := D.U.ι ≫ D.π₂) (g := D.V.ι ≫ D.π₁)), divl, Category.assoc,
        Category.assoc, ← D.hP.w, D.linv_fst_assoc])

@[reassoc (attr := simp)]
theorem FM_fst : D.FM ≫ D.π₁ = pullback.fst _ _ ≫ D.m := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem FM_snd : D.FM ≫ D.π₂ = pullback.snd _ _ ≫ D.divl := D.hP.lift_snd _ _ _

def ΩM : D.ZM.Opens := D.FM ⁻¹ᵁ D.U

def pM : (D.ΩM : Scheme.{u}) ⟶ D.P := D.ΩM.ι ≫ D.jM ≫ D.outer

def ppM : (D.ΩM : Scheme.{u}) ⟶ D.U := D.FM.resLE D.U _ le_rfl

@[reassoc]
theorem ppM_ι : D.ppM ≫ D.U.ι = D.ΩM.ι ≫ D.FM := Scheme.Hom.resLE_comp_ι _ _

def fM : (D.ΩM : Scheme.{u}) ⟶ D.Y := D.ppM ≫ D.m

@[reassoc]
theorem pM_fst : D.pM ≫ D.π₁ = D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ := by
  rw [pM, Category.assoc, Category.assoc, outer_fst, jM_P12_assoc]

@[reassoc]
theorem pM_snd : D.pM ≫ D.π₂ = D.ΩM.ι ≫ pullback.snd _ _ ≫ D.V.ι ≫ D.π₂ := by
  rw [pM, Category.assoc, Category.assoc, outer_snd, jM_P23_assoc]

scoped instance smooth_pM : Smooth D.pM := by rw [pM]; infer_instance

theorem surjective_pM (hU₁ : D.FibDense D.π₁ D.U) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) : Surjective D.pM := by
  refine ⟨fun t => ?_⟩

  obtain ⟨ω, hωt, hω⟩ := exists_fibMax D.outer t (D.outer.surjective.range_eq ▸ trivial)

  have h12 : FibMax D.π₁ (D.P12.base ω) := fibMax_fst_of_isPullback D.isPullback_P12_outer hω
  have h23 : FibMax D.π₂ (D.P23.base ω) := fibMax_fst_of_isPullback D.isPullback_P23_outer hω
  have hU : D.P12.base ω ∈ D.U := mem_of_dense_fibre_of_fibMax D.π₁ D.U _ (hU₁ _) rfl h12
  have hV : D.P23.base ω ∈ D.V :=
    mem_of_dense_fibre_of_fibMax D.π₂ D.V _ (by rw [coe_V]; exact hV₂ _) rfl h23

  obtain ⟨ζ, hζ⟩ : ω ∈ Set.range D.jM.base := by
    rw [jM, Scheme.Pullback.range_map]
    exact ⟨by rw [Scheme.Opens.range_ι]; exact hU, by rw [Scheme.Opens.range_ι]; exact hV⟩

  have hsq := D.hP.flip
  have hu : D.U.ι.base (pullback.fst (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) = D.P12.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jM_P12, Scheme.Hom.comp_apply, hζ]
  have hv : D.V.ι.base (pullback.snd (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) = D.P23.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jM_P23, Scheme.Hom.comp_apply, hζ]
  have h1 : D.π₁.base (D.FM.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FM_fst, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 : FibMax (D.U.ι ≫ D.π₁) (pullback.fst (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ) :=
      fibMax_comp_of_injective D.U.ι D.π₁ D.U.ι.isOpenEmbedding.injective (hu ▸ h12)
    rw [← D.Φ_fst] at k1
    have k2 := fibMax_of_isOpenImmersion D.Φ D.π₁ k1
    have k3 := fibMax_fst_of_isPullback hsq k2
    rwa [← Scheme.Hom.comp_apply, D.Φ_snd] at k3
  have h2 : D.π₂.base (D.FM.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FM_snd, Scheme.Hom.comp_apply, divl, Scheme.Hom.comp_apply]
    apply hY₀
    have k0 : FibMax D.π₂ (D.Φ.base (D.linv.base (pullback.snd (D.U.ι ≫ D.π₂) (D.V.ι ≫ D.π₁) ζ))) := by
      rw [← Scheme.Hom.comp_apply, linv_Φ, hv]; exact h23
    have k1 := fibMax_comp_of_injective D.Φ D.π₂ D.Φ.isOpenEmbedding.injective k0
    rw [D.Φ_snd, ← D.Ψ_fst] at k1
    have k2 := fibMax_of_isOpenImmersion D.Ψ D.π₁ k1
    have k3 := fibMax_fst_of_isPullback hsq k2
    rwa [← Scheme.Hom.comp_apply, D.Ψ_snd] at k3
  have hζΩ : ζ ∈ D.ΩM := hY₀U _ h1 h2
  refine ⟨⟨ζ, hζΩ⟩, ?_⟩
  rw [pM, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hζ, hωt]

theorem fM_agree (hassoc : D.Assoc) :
    (D.pM ⁻¹ᵁ D.U).ι ≫ D.fM = D.pM.resLE D.U _ le_rfl ≫ D.m := by
  set Ω' := D.pM ⁻¹ᵁ D.U
  let t : (Ω' : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y
  have hcond : Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₂ =
      Ω'.ι ≫ D.ΩM.ι ≫ pullback.snd _ _ ≫ D.V.ι ≫ D.π₁ := by
    rw [pullback.condition]
  let uu : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩM.ι ≫ pullback.fst _ _, by simp only [t, Category.assoc]⟩
  let vv : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩM.ι ≫ pullback.snd _ _ ≫ D.linv, by
      simp only [t, Category.assoc]
      rw [D.linv_fst_assoc]
      conv_rhs => rw [D.hP.w]
      rw [reassoc_of% hcond]⟩
  let pp : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ppM, by
      simp only [t, Category.assoc]
      rw [D.ppM_ι_assoc, FM_fst_assoc, D.hm]⟩
  let qq : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨D.pM.resLE D.U _ le_rfl, by
      simp only [t, Category.assoc]
      rw [Scheme.Hom.resLE_comp_ι_assoc, pM_fst_assoc]⟩
  have key := hassoc t uu vv pp qq
    (by simp only [uu, vv, Category.assoc]; rw [D.linv_fst, hcond])
    (by simp only [pp, uu, Category.assoc]; rw [D.ppM_ι_assoc, FM_fst])
    (by simp only [pp, vv, Category.assoc]; rw [D.ppM_ι_assoc, FM_snd, divl])
    (by simp only [qq, uu, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, pM_fst])
    (by simp only [qq, vv, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, pM_snd, D.linv_m])
  simpa only [pp, qq, fM, Category.assoc] using key

theorem exists_M [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc) (hU₁ : D.FibDense D.π₁ D.U)
    (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base)) (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) :
    ∃ M : D.P ⟶ D.Y, D.U.ι ≫ M = D.m ∧ M ≫ D.y = D.π₁ ≫ D.y := by
  haveI := D.isReduced_P
  haveI := D.surjective_pM hU₁ hV₂ Y₀ hY₀ hY₀U
  haveI : IsReduced (pullback D.pM D.pM) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst D.pM D.pM ≫ D.ΩM.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y)
  have hUd : Dense (D.U : Set D.P) := dense_of_forall_dense_fibre D.π₁ _ hU₁
  have hf' : D.fM ≫ D.y = D.pM ≫ D.π₁ ≫ D.y := by
    rw [fM, Category.assoc, D.hm, D.ppM_ι_assoc, FM_fst_assoc, D.hm, pM_fst_assoc]
  obtain ⟨M, -, hMm, hMy⟩ := exists_extension_of_descent (D.π₁ ≫ D.y) D.y D.U D.m D.hm D.pM D.fM hf'
    (D.pM ⁻¹ᵁ D.U) (hUd.preimage D.pM.isOpenMap) le_rfl (D.fM_agree hassoc)
  exact ⟨M, hMm, hMy⟩

section Division

variable (M : D.P ⟶ D.Y) (hMm : D.U.ι ≫ M = D.m) (hMy : M ≫ D.y = D.π₁ ≫ D.y)

abbrev ZD : Scheme.{u} := pullback D.m (D.U.ι ≫ D.π₁)

def jD : D.ZD ⟶ D.Y3 :=
  pullback.map D.m (D.U.ι ≫ D.π₁) D.π₂ D.π₁ D.Φ D.Φ (𝟙 D.Y)
    ((Category.comp_id _).trans D.Φ_snd.symm) ((Category.comp_id _).trans D.Φ_fst.symm)

scoped instance : IsOpenImmersion D.jD :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance D.Φ_snd.symm D.Φ_fst.symm

@[reassoc (attr := simp)]
theorem jD_P12 : D.jD ≫ D.P12 = pullback.fst _ _ ≫ D.Φ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jD_P23 : D.jD ≫ D.P23 = pullback.snd _ _ ≫ D.Φ := pullback.lift_snd _ _ _

def FD : D.ZD ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.U.ι ≫ D.π₂) (pullback.snd _ _ ≫ D.U.ι ≫ D.π₂)
    (by
      simp only [Category.assoc]
      conv_lhs => rw [← D.hP.w, ← D.hm]
      rw [pullback.condition_assoc, Category.assoc, D.hP.w])

@[reassoc (attr := simp)]
theorem FD_fst : D.FD ≫ D.π₁ = pullback.fst _ _ ≫ D.U.ι ≫ D.π₂ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem FD_snd : D.FD ≫ D.π₂ = pullback.snd _ _ ≫ D.U.ι ≫ D.π₂ := D.hP.lift_snd _ _ _

def ΩD : D.ZD.Opens := D.FD ⁻¹ᵁ D.U

def pD : (D.ΩD : Scheme.{u}) ⟶ D.P := D.ΩD.ι ≫ D.jD ≫ D.outer

def ppD : (D.ΩD : Scheme.{u}) ⟶ D.U := D.FD.resLE D.U _ le_rfl

@[reassoc]
theorem ppD_ι : D.ppD ≫ D.U.ι = D.ΩD.ι ≫ D.FD := Scheme.Hom.resLE_comp_ι _ _

def fD : (D.ΩD : Scheme.{u}) ⟶ D.Y := D.ppD ≫ D.m

@[reassoc]
theorem pD_fst : D.pD ≫ D.π₁ = D.ΩD.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ := by
  rw [pD, Category.assoc, Category.assoc, outer_fst, jD_P12_assoc, D.Φ_fst]

@[reassoc]
theorem pD_snd : D.pD ≫ D.π₂ = D.ΩD.ι ≫ pullback.snd _ _ ≫ D.m := by
  rw [pD, Category.assoc, Category.assoc, outer_snd, jD_P23_assoc, D.Φ_snd]

scoped instance smooth_pD : Smooth D.pD := by rw [pD]; infer_instance

theorem fD_y : D.fD ≫ D.y = D.pD ≫ D.π₁ ≫ D.y := by
  rw [fD, Category.assoc, D.hm, D.ppD_ι_assoc, FD_fst_assoc, ← D.hP.w, pD_fst_assoc]

def GD : (D.ΩD : Scheme.{u}) ⟶ D.P :=
  D.hP.lift (D.pD ≫ D.π₁) D.fD (by rw [Category.assoc, fD_y])

@[reassoc (attr := simp)]
theorem GD_fst : D.GD ≫ D.π₁ = D.pD ≫ D.π₁ := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem GD_snd : D.GD ≫ D.π₂ = D.fD := D.hP.lift_snd _ _ _

def ΩD' : (D.ΩD : Scheme.{u}).Opens := D.pD ⁻¹ᵁ D.V ⊓ D.GD ⁻¹ᵁ D.U

theorem surjective_pD (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base))
    (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) : Surjective D.pD := by
  refine ⟨fun t => ?_⟩
  obtain ⟨ω, hωt, hω⟩ := exists_fibMax D.outer t (D.outer.surjective.range_eq ▸ trivial)
  have h12 : FibMax D.π₁ (D.P12.base ω) := fibMax_fst_of_isPullback D.isPullback_P12_outer hω
  have h23 : FibMax D.π₂ (D.P23.base ω) := fibMax_fst_of_isPullback D.isPullback_P23_outer hω
  have hV12 : D.P12.base ω ∈ Set.range D.Φ.base :=
    mem_of_dense_fibre_of_fibMax D.π₁ D.V _ (by rw [coe_V]; exact hV₁ _) rfl h12
  have hV23 : D.P23.base ω ∈ Set.range D.Φ.base :=
    mem_of_dense_fibre_of_fibMax D.π₂ D.V _ (by rw [coe_V]; exact hV₂ _) rfl h23
  obtain ⟨ζ, hζ⟩ : ω ∈ Set.range D.jD.base := by
    rw [jD, Scheme.Pullback.range_map]; exact ⟨hV12, hV23⟩
  have hsq := D.hP.flip
  have hu : D.Φ.base (pullback.fst D.m (D.U.ι ≫ D.π₁) ζ) = D.P12.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jD_P12, Scheme.Hom.comp_apply, hζ]
  have hv : D.Φ.base (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ) = D.P23.base ω := by
    rw [← Scheme.Hom.comp_apply, ← jD_P23, Scheme.Hom.comp_apply, hζ]
  have h1 : D.π₁.base (D.FD.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FD_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 := fibMax_comp_of_injective D.Φ D.π₁ D.Φ.isOpenEmbedding.injective (hu ▸ h12)
    rw [D.Φ_fst] at k1
    exact fibMax_fst_of_isPullback hsq (fibMax_of_isOpenImmersion D.U.ι D.π₁ k1)
  have h2 : D.π₂.base (D.FD.base ζ) ∈ Y₀ := by
    rw [← Scheme.Hom.comp_apply, FD_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    apply hY₀
    have k1 := fibMax_comp_of_injective D.Φ D.π₂ D.Φ.isOpenEmbedding.injective (hv ▸ h23)
    rw [D.Φ_snd] at k1
    have k1' : FibMax (D.Ψ ≫ D.π₁) (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ) := by rw [D.Ψ_fst]; exact k1
    have k3 := fibMax_fst_of_isPullback hsq (fibMax_of_isOpenImmersion D.Ψ D.π₁ k1')
    rwa [← Scheme.Hom.comp_apply, D.Ψ_snd, Scheme.Hom.comp_apply] at k3
  have hζΩ : ζ ∈ D.ΩD := hY₀U _ h1 h2
  refine ⟨⟨ζ, hζΩ⟩, ?_⟩
  rw [pD, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, hζ, hωt]

theorem fD_agree (hassoc : D.Assoc) :
    D.ΩD'.ι ≫ D.fD = D.pD.resLE D.V D.ΩD' inf_le_left ≫ D.divl := by
  set Ω' := D.ΩD'
  let t : (Ω' : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _ ≫ D.U.ι ≫ D.π₁ ≫ D.y
  have hcond : Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _ ≫ D.m = Ω'.ι ≫ D.ΩD.ι ≫ pullback.snd _ _ ≫ D.U.ι ≫ D.π₁ := by
    rw [pullback.condition]
  let uu : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩD.ι ≫ pullback.fst _ _, by simp only [t, Category.assoc]⟩
  let vv : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ppD, by
      simp only [t, Category.assoc]
      rw [D.ppD_ι_assoc, FD_fst_assoc, ← D.hP.w]⟩
  let pp : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨Ω'.ι ≫ D.ΩD.ι ≫ pullback.snd _ _, by
      simp only [t, Category.assoc]
      rw [← reassoc_of% hcond, D.hm]⟩
  let qq : NeronModelInfra.SchemeHomOver t (D.U.ι ≫ D.π₁ ≫ D.y) :=
    ⟨D.GD.resLE D.U _ inf_le_right, by
      simp only [t, Category.assoc]
      rw [Scheme.Hom.resLE_comp_ι_assoc, GD_fst_assoc, pD_fst_assoc]⟩
  have key := hassoc t uu vv pp qq
    (by simp only [uu, vv, Category.assoc]; rw [D.ppD_ι_assoc, FD_fst])
    (by simp only [pp, uu, Category.assoc]; rw [hcond])
    (by simp only [pp, vv, Category.assoc]; rw [D.ppD_ι_assoc, FD_snd])
    (by simp only [qq, uu, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, GD_fst, pD_fst])
    (by simp only [qq, vv, Category.assoc]; rw [Scheme.Hom.resLE_comp_ι_assoc, GD_snd, fD])

  have hqΦ : qq.1 ≫ D.Φ = Ω'.ι ≫ D.pD := by
    refine D.hP.hom_ext ?_ ?_
    · rw [Category.assoc, D.Φ_fst, Scheme.Hom.resLE_comp_ι_assoc, GD_fst, Category.assoc]
    · rw [Category.assoc, D.Φ_snd, ← key]
      simp only [pp, Category.assoc]
      rw [pD_snd]
  have hρ : D.pD.resLE D.V Ω' inf_le_left ≫ D.linv = qq.1 := by
    rw [← cancel_mono D.Φ, Category.assoc, D.linv_Φ, Scheme.Hom.resLE_comp_ι, hqΦ]
  rw [divl, reassoc_of% hρ]
  simp only [qq]
  rw [Scheme.Hom.resLE_comp_ι_assoc, GD_snd]

abbrev BD : Scheme.{u} := pullback (D.U.ι ≫ D.π₂) D.π₁

def KD : D.BD ⟶ D.P :=
  D.hP.lift (pullback.fst _ _ ≫ D.m) (pullback.snd _ _ ≫ D.π₂)
    (by
      rw [Category.assoc, D.hm, Category.assoc, D.hP.w,
        reassoc_of% (pullback.condition (f := D.U.ι ≫ D.π₂) (g := D.π₁)), D.hP.w])

@[reassoc (attr := simp)]
theorem KD_fst : D.KD ≫ D.π₁ = pullback.fst _ _ ≫ D.m := D.hP.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem KD_snd : D.KD ≫ D.π₂ = pullback.snd _ _ ≫ D.π₂ := D.hP.lift_snd _ _ _

def BD' : D.BD.Opens := D.KD ⁻¹ᵁ D.U

def HD : (D.BD' : Scheme.{u}) ⟶ D.ZD :=
  pullback.lift (D.BD'.ι ≫ pullback.fst _ _) (D.KD.resLE D.U _ le_rfl)
    (by rw [Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, KD_fst])

theorem HD_FD : D.HD ≫ D.FD = D.BD'.ι ≫ pullback.snd _ _ := by
  refine D.hP.hom_ext ?_ ?_
  · rw [Category.assoc, FD_fst, HD, pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition]
  · rw [Category.assoc, FD_snd, HD, pullback.lift_snd_assoc, Scheme.Hom.resLE_comp_ι_assoc, KD_snd,
      Category.assoc]

def LD : D.ZD ⟶ D.BD := pullback.lift (pullback.fst _ _) D.FD (by rw [FD_fst])

theorem LD_KD : D.LD ≫ D.KD = pullback.snd _ _ ≫ D.U.ι := by
  refine D.hP.hom_ext ?_ ?_
  · rw [Category.assoc, KD_fst, LD, pullback.lift_fst_assoc, Category.assoc, pullback.condition]
  · rw [Category.assoc, KD_snd, LD, pullback.lift_snd_assoc, FD_snd, Category.assoc]

theorem range_LD : Set.range D.LD.base ⊆ Set.range D.BD'.ι.base := by
  rintro _ ⟨ζ, rfl⟩
  rw [Scheme.Opens.range_ι]
  change D.KD.base (D.LD.base ζ) ∈ D.U
  rw [← Scheme.Hom.comp_apply, LD_KD, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact (pullback.snd D.m (D.U.ι ≫ D.π₁) ζ).2

def LD' : D.ZD ⟶ D.BD' := IsOpenImmersion.lift D.BD'.ι D.LD D.range_LD

theorem LD'_HD : D.LD' ≫ D.HD = 𝟙 _ := by
  have e : D.LD' ≫ D.BD'.ι = D.LD := IsOpenImmersion.lift_fac _ _ _
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, HD, pullback.lift_fst, reassoc_of% e, LD, pullback.lift_fst, Category.id_comp]
  · rw [← cancel_mono D.U.ι, Category.assoc, Category.assoc, HD, pullback.lift_snd_assoc,
      Scheme.Hom.resLE_comp_ι, reassoc_of% e, LD_KD, Category.id_comp]

theorem maximal_FD {ζ : D.ZD} (hζ : ∀ x', x' ⤳ ζ → x' = ζ) (q' : D.P) (hq' : q' ⤳ D.FD.base ζ) :
    q' = D.FD.base ζ := by
  revert q' hq'

  refine maximal_of_dominated D.FD D.HD (D.BD'.ι ≫ pullback.snd _ _)
    (Flat.generalizingMap _) D.HD_FD (b := D.LD'.base ζ) ?_ hζ
  rw [← Scheme.Hom.comp_apply, LD'_HD]; rfl

theorem dense_ΩD' (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) : Dense (D.ΩD' : Set D.ΩD) := by
  have hVd : Dense (D.V : Set D.P) := by rw [coe_V]; exact dense_of_forall_dense_fibre D.π₁ _ hV₁
  have h1 : Dense ((D.pD ⁻¹ᵁ D.V : (D.ΩD : Scheme.{u}).Opens) : Set D.ΩD) := hVd.preimage D.pD.isOpenMap
  have h2 := h1.inter_of_isOpen_left
    (dense_of_forall_maximal_mem (X := D.ΩD) (S := {x | ∀ x', x' ⤳ x → x' = x}) fun x hx => hx)
    (D.pD ⁻¹ᵁ D.V).isOpen
  refine h2.mono ?_
  rintro ζ ⟨hζV, hζmax⟩
  refine ⟨hζV, ?_⟩
  change D.GD.base ζ ∈ D.U
  apply hY₀U
  · rw [← Scheme.Hom.comp_apply, GD_fst, Scheme.Hom.comp_apply]
    apply hY₀
    exact fibMax_of_maximal _ (maximal_of_generalizingMap D.π₁ (Flat.generalizingMap _)
      (maximal_of_generalizingMap D.pD (Flat.generalizingMap _) hζmax))
  · rw [← Scheme.Hom.comp_apply, GD_snd, fD, Scheme.Hom.comp_apply]
    apply hY₀
    apply fibMax_of_maximal
    have hm : GeneralizingMap D.m.base := by
      rw [← D.Ψ_fst]; exact (Flat.generalizingMap D.Ψ).comp (Flat.generalizingMap D.π₁)
    apply maximal_of_generalizingMap D.m hm
    apply maximal_of_injective D.U.ι D.U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ppD_ι, Scheme.Hom.comp_apply]
    exact D.maximal_FD (maximal_of_generalizingMap D.ΩD.ι (Flat.generalizingMap _) hζmax)

theorem exists_Dv [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) :
    ∃ Dv : D.P ⟶ D.Y, D.V.ι ≫ Dv = D.divl ∧ Dv ≫ D.y = D.π₁ ≫ D.y := by
  haveI := D.isReduced_P
  haveI := D.surjective_pD hV₁ hV₂ Y₀ hY₀ hY₀U
  haveI : IsReduced (pullback D.pD D.pD) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst D.pD D.pD ≫ D.ΩD.ι ≫ pullback.fst D.m (D.U.ι ≫ D.π₁) ≫ D.U.ι ≫ D.π₁ ≫ D.y)
  have hf : D.divl ≫ D.y = D.V.ι ≫ D.π₁ ≫ D.y := by
    rw [divl, Category.assoc, Category.assoc, ← D.hP.w, D.linv_fst_assoc]
  obtain ⟨Dv, -, hDv, hDy⟩ := exists_extension_of_descent (D.π₁ ≫ D.y) D.y D.V D.divl hf D.pD D.fD D.fD_y
    D.ΩD' (D.dense_ΩD' Y₀ hY₀ hY₀U hV₁) inf_le_left (D.fD_agree hassoc)
  exact ⟨Dv, hDv, hDy⟩

include hMm hMy in

theorem isIso_translation [IsDomain R] [IsDiscreteValuationRing R] (hassoc : D.Assoc)
    (hV₁ : D.FibDense D.π₁ (Set.range D.Φ.base)) (hV₂ : D.FibDense D.π₂ (Set.range D.Φ.base))
    (Y₀ : D.Y.Opens) (hY₀ : D.MaxMem Y₀) (hY₀U : D.SqSub Y₀) :
    IsIso (D.hP.lift D.π₁ M (by rw [hMy])) := by
  haveI := D.isReduced_P
  haveI : IsSeparated D.π₁ := MorphismProperty.of_isPullback D.hP.flip inferInstance
  obtain ⟨Dv, hDv, hDy⟩ := D.exists_Dv hassoc hV₁ hV₂ Y₀ hY₀ hY₀U
  set ΦM := D.hP.lift D.π₁ M (by rw [hMy])
  let N : D.P ⟶ D.P := D.hP.lift D.π₁ Dv (by rw [hDy])
  have hUΦM : D.U.ι ≫ ΦM = D.Φ := by
    refine D.hP.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, D.Φ_fst]
    · rw [Category.assoc, IsPullback.lift_snd, hMm, D.Φ_snd]
  have hVN : D.V.ι ≫ N = D.linv ≫ D.U.ι := by
    refine D.hP.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, Category.assoc, D.linv_fst]
    · rw [Category.assoc, IsPullback.lift_snd, hDv, divl, Category.assoc]

  have hVd : Dense (D.V : Set D.P) := by rw [coe_V]; exact dense_of_forall_dense_fibre D.π₁ _ hV₁
  have hUd : Dense (D.U : Set D.P) := by
    refine dense_of_forall_maximal_mem fun q hq => hY₀U q ?_ ?_
    · exact hY₀ _ (fibMax_of_maximal _ (maximal_of_generalizingMap D.π₁ (Flat.generalizingMap _) hq))
    · exact hY₀ _ (fibMax_of_maximal _ (maximal_of_generalizingMap D.π₂ (Flat.generalizingMap _) hq))
  haveI : IsDominant D.U.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hUd⟩
  haveI : IsDominant D.V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hVd⟩
  refine ⟨N, ?_, ?_⟩
  · refine ext_of_isDominant_of_isSeparated (D.π₁ ≫ D.y) ?_ D.U.ι ?_
    · rw [Category.assoc, IsPullback.lift_fst_assoc, IsPullback.lift_fst_assoc, Category.id_comp]
    · rw [Category.comp_id, reassoc_of% hUΦM, ← D.Φ.isoOpensRange_hom_ι, Category.assoc, hVN,
        Iso.hom_inv_id_assoc]
  · refine ext_of_isDominant_of_isSeparated (D.π₁ ≫ D.y) ?_ D.V.ι ?_
    · rw [Category.assoc, IsPullback.lift_fst_assoc, IsPullback.lift_fst_assoc, Category.id_comp]
    · rw [Category.comp_id, reassoc_of% hVN, hUΦM, D.linv_Φ]

end Division

end Chunk
p2m_reactivate "P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.P2mGExt.Chunk"

end P2mGExt
p2m_reactivate "P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.P2mGExt.Chunk P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.P2mGExt"

open NeronModelInfra GoodReductionJacobian

set_option linter.unusedVariables false in
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
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    (Y₀ : Y.Opens)
    (hY₀ : ∀ p : Y, (∀ p' : Y, p' ⤳ p → y.base p' = y.base p → p' = p) → p ∈ Y₀)
    (hY₀U : ∀ q : ↑(pullback y y), (pullback.fst y y).base q ∈ Y₀ → (pullback.snd y y).base q ∈ Y₀ → q ∈ U) :
    ∃ M : SchemeHomOver (pullback.fst y y ≫ y) y,
      U.ι ≫ M.1 = m.1 ∧
      IsIso (pullback.lift (f := y) (g := y) (pullback.fst y y) M.1 M.2.symm) ∧
      IsIso (pullback.lift (f := y) (g := y) M.1 (pullback.snd y y) (M.2.trans pullback.condition)) := by

  haveI : Surjective y := ⟨fun s => ⟨a.base s, by rw [← Scheme.Hom.comp_apply, ha]; rfl⟩⟩
  haveI := hΦ
  haveI := hΨ

  let D : P2mGExt.Chunk R :=
    { Y := Y, P := pullback y y, y := y, π₁ := pullback.fst y y, π₂ := pullback.snd y y,
      hP := IsPullback.of_hasPullback y y, U := U, m := m.1, hm := m.2,
      Φ := pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm),
      Ψ := pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition])),
      Φ_fst := pullback.lift_fst _ _ _, Φ_snd := pullback.lift_snd _ _ _,
      Ψ_fst := pullback.lift_fst _ _ _, Ψ_snd := pullback.lift_snd _ _ _,
      Φ_open := hΦ, Ψ_open := hΨ, y_smooth := inferInstance, y_sep := inferInstance,
      π₁_smooth := inferInstance, π₂_smooth := inferInstance, π₁_surj := inferInstance, π₂_surj := inferInstance }
  have hassoc' : D.Assoc := fun t u v p q => hassoc t u v p q
  have hU₁' : D.FibDense D.π₁ D.U := hU₁
  have hV₁' : D.FibDense D.π₁ (Set.range D.Φ.base) := hΦ₁
  have hV₂' : D.FibDense D.π₂ (Set.range D.Φ.base) := hΦ₂
  have hW₁' : D.flip.FibDense D.flip.π₂ (Set.range D.flip.Φ.base) := hΨ₁
  have hW₂' : D.flip.FibDense D.flip.π₁ (Set.range D.flip.Φ.base) := hΨ₂
  have hY₀' : D.MaxMem Y₀ := hY₀
  have hY₀U' : D.SqSub Y₀ := hY₀U

  obtain ⟨M, hMm, hMy⟩ := D.exists_M hassoc' hU₁' hV₂' Y₀ hY₀' hY₀U'
  have h1 := D.isIso_translation M hMm hMy hassoc' hV₁' hV₂' Y₀ hY₀' hY₀U'
  have hMy' : M ≫ D.flip.y = D.flip.π₁ ≫ D.flip.y := hMy.trans pullback.condition
  have h2 := D.flip.isIso_translation M hMm hMy' (D.assoc_flip hassoc') hW₂' hW₁' Y₀ hY₀' (D.sqSub_flip hY₀U')
  refine ⟨⟨M, hMy⟩, hMm, ?_, ?_⟩
  · have e : pullback.lift (f := y) (g := y) (pullback.fst y y) M hMy.symm = D.hP.lift D.π₁ M hMy.symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]; exact (D.hP.lift_fst _ _ _).symm
      · rw [pullback.lift_snd]; exact (D.hP.lift_snd _ _ _).symm
    rw [e]; exact h1
  · have e : pullback.lift (f := y) (g := y) M (pullback.snd y y) (hMy.trans pullback.condition) =
        D.flip.hP.lift D.flip.π₁ M hMy'.symm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]; exact (D.flip.hP.lift_snd _ _ _).symm
      · rw [pullback.lift_snd]; exact (D.flip.hP.lift_fst _ _ _).symm
    rw [e]; exact h2

end
end S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
end P2MW
export P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section (solution)
