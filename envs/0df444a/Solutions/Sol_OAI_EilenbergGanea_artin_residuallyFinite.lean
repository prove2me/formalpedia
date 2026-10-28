-- Prove2me | solution 1 for OAI.EilenbergGanea.artin_residuallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:26:28.829636+00:00
-- url     : https://prove2.me/submissions/00407ce1-0c86-4297-8949-b06bcf4e1985

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC003

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/
section FreeGroupResidualFiniteness

variable {A : Type*} [Group A]

theorem finiteTranslation_apply (s : Finset A) (a : A) (x : s)
    (hx : a * x.val ∈ s) : (finiteTranslation s a x).val = a * x.val :=
  (finite_translation_extension s a).choose_spec x hx

theorem finiteTranslation_inv_apply (s : Finset A) (a : A) (x : s)
    (hx : a⁻¹ * x.val ∈ s) : ((finiteTranslation s a)⁻¹ x).val = a⁻¹ * x.val := by
  let y : s := ⟨a⁻¹ * x.val, hx⟩
  have he : finiteTranslation s a y = x := by
    apply Subtype.ext
    have hm : a * y.val ∈ s := by simp [y]
    rw [finiteTranslation_apply s a y hm]
    simp [y]
  have hi := congrArg (finiteTranslation s a).symm he
  simpa [y] using (congrArg Subtype.val hi).symm

variable {X : Type*}

theorem mk_mem_wordVertices (w : List (X × Bool)) : FreeGroup.mk w ∈ wordVertices w := by
  classical
  simp only [wordVertices, List.mem_toFinset, List.mem_map]
  exact ⟨w, by simp, rfl⟩

theorem one_mem_wordVertices (w : List (X × Bool)) : (1 : FreeGroup X) ∈ wordVertices w := by
  classical
  simp only [wordVertices, List.mem_toFinset, List.mem_map]
  exact ⟨[], by simp, rfl⟩

theorem wordVertices_tail_subset (x : X × Bool) (w : List (X × Bool)) :
    wordVertices w ⊆ wordVertices (x :: w) := by
  classical
  simp only [wordVertices, List.tails_cons, List.map_cons, List.toFinset_cons]
  exact Finset.subset_insert _ _

theorem mk_cons_sign (a : X) (b : Bool) (w : List (X × Bool)) :
    FreeGroup.mk ((a, b) :: w) =
      (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk w := by
  cases b <;> rfl

/-- Whenever a finite set includes all suffix vertices, the finite action follows
that word exactly starting at the identity. No reduced-word choice is needed. -/
theorem finiteWordAction_tracks (s : Finset (FreeGroup X)) (w : List (X × Bool))
    (hw : wordVertices w ⊆ s) (h1 : (1 : FreeGroup X) ∈ s) :
    (finiteWordAction s (FreeGroup.mk w) ⟨1, h1⟩).val = FreeGroup.mk w := by
  induction w with
  | nil => simp [finiteWordAction, FreeGroup.one_eq_mk]
  | cons x w ih =>
    have ht := ih ((wordVertices_tail_subset x w).trans hw)
    have hm := hw (mk_mem_wordVertices (x :: w))
    rcases x with ⟨a, b⟩
    rw [mk_cons_sign] at hm ⊢
    rw [map_mul]
    change ((finiteWordAction s (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹))
      (finiteWordAction s (FreeGroup.mk w) ⟨1, h1⟩)).val = _
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv,
        finiteWordAction, FreeGroup.lift_apply_of]
      rw [finiteTranslation_inv_apply]
      · exact congrArg ((FreeGroup.of a)⁻¹ * ·) ht
      · change (FreeGroup.of a)⁻¹ * (finiteWordAction s (FreeGroup.mk w) ⟨1, h1⟩).val ∈ s
        rw [ht]; exact hm
    · simp only [↓reduceIte, finiteWordAction, FreeGroup.lift_apply_of]
      rw [finiteTranslation_apply]
      · exact congrArg (FreeGroup.of a * ·) ht
      · change FreeGroup.of a * (finiteWordAction s (FreeGroup.mk w) ⟨1, h1⟩).val ∈ s
        rw [ht]; exact hm

/-- Free groups on arbitrary types are residually finite; this is proved using
finite partial translations, not assumed as a literature result. -/
theorem freeGroup_residuallyFinite (X : Type*) : Group.ResiduallyFinite (FreeGroup X) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let s := wordVertices g.toWord
  have h1 : (1 : FreeGroup X) ∈ s := one_mem_wordVertices _
  refine ⟨Equiv.Perm s, inferInstance, inferInstance, finiteWordAction s, ?_⟩
  intro he
  have ht := finiteWordAction_tracks s g.toWord (Finset.Subset.refl s) h1
  rw [FreeGroup.mk_toWord, he] at ht
  change (1 : FreeGroup X) = g at ht
  exact hg ht.symm

end FreeGroupResidualFiniteness


section FiniteSemidirectSeparation

variable {N D K : Type*} [Group N] [Group D] [Group K]

theorem orbitObservation_equivariant (φ : D →* MulAut N) (f : N →* K) (d : D) :
    (orbitObservation φ f).comp (φ d).toMonoidHom =
      (functionShift D K d).toMonoidHom.comp (orbitObservation φ f) := by
  ext n e
  simp [orbitObservation, functionShift, map_mul]

/-- A finite extension of a residually finite group is residually finite.
Only the semidirect form needed by the source is used. -/
theorem finite_semidirect_residuallyFinite [Finite D] [Group.ResiduallyFinite N]
    (φ : D →* MulAut N) : Group.ResiduallyFinite (N ⋊[φ] D) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro x hx
  by_cases hd : x.right = 1
  · have hn : x.left ≠ 1 := by
      intro he
      apply hx
      ext <;> assumption
    obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem x.left hn
    let f : N →* N ⧸ H.toSubgroup := QuotientGroup.mk' H.toSubgroup
    let F := orbitObservation φ f
    let ψ := functionShift D (N ⧸ H.toSubgroup)
    let q : (N ⋊[φ] D) →* ((D → N ⧸ H.toSubgroup) ⋊[ψ] D) :=
      SemidirectProduct.map F (MonoidHom.id D) (orbitObservation_equivariant φ f)
    refine ⟨_, inferInstance, ?_, q, ?_⟩
    · exact Finite.of_equiv ((D → N ⧸ H.toSubgroup) × D)
        SemidirectProduct.equivProd.symm
    · intro he
      have hv := congrArg (fun y => y.left (1 : D)) he
      have hz : f x.left = 1 := by simpa [q, F, orbitObservation] using hv
      exact hH ((QuotientGroup.eq_one_iff _).mp hz)
  · let q : (N ⋊[φ] D) →* D × (N ⧸ (⊤ : Subgroup N)) :=
      SemidirectProduct.rightHom.prod 1
    refine ⟨_, inferInstance, inferInstance, q, ?_⟩
    intro he
    exact hd (congrArg Prod.fst he)

end FiniteSemidirectSeparation


section FreeAction

variable (A X : Type*) [Group A] [MulAction A X]

variable {A X} {B Y : Type*} [Group B] [MulAction B Y]

theorem freeAction_map_equivariant (q : A →* B) (f : X → Y)
    (hf : ∀ a x, f (a • x) = q a • f x) (a : A) :
    (FreeGroup.map f).comp (freeAction A X a).toMonoidHom =
      (freeAction B Y (q a)).toMonoidHom.comp (FreeGroup.map f) := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, freeAction_of,
    FreeGroup.map.of, hf]

end FreeAction


section FiniteQuotientSeparation

variable {A : Type*} [Group A] [Group.ResiduallyFinite A]

/-- Finitely many nonidentity elements can be excluded by one finite quotient. -/
theorem finite_nonidentity_separation (s : Finset A) :
    ∃ H : FiniteIndexNormalSubgroup A, ∀ a ∈ s, a ≠ 1 → a ∉ H := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨.ofSubgroup ⊤, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨H, hH⟩ := ih
    by_cases h1 : a = 1
    · refine ⟨H, ?_⟩
      intro b hb hb1
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hb1 h1).elim
      · exact hH b hb hb1
    · obtain ⟨K, hK⟩ := Group.exists_finiteIndexNormalSubgroup_notMem a h1
      refine ⟨H ⊓ K, ?_⟩
      intro b hb hb1 hm
      change b ∈ H.toSubgroup ⊓ K.toSubgroup at hm
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hK hm.2
      · exact hH b hb hb1 hm.1

/-- The exact finite-set injectivity consequence of residual finiteness. -/
theorem finite_set_quotient_injective (s : Finset A) :
    ∃ H : FiniteIndexNormalSubgroup A,
      Set.InjOn (QuotientGroup.mk' H.toSubgroup) (s : Set A) := by
  classical
  obtain ⟨H, hH⟩ := finite_nonidentity_separation
    ((s ×ˢ s).image (fun z => z.1⁻¹ * z.2))
  refine ⟨H, ?_⟩
  intro a ha b hb he
  by_contra hn
  apply hH (a⁻¹ * b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
    (fun h => hn (eq_of_inv_mul_eq_one h))
  exact QuotientGroup.eq.mp he

end FiniteQuotientSeparation

section RetractCosetSeparation

variable {A : Type u} {D : Type*} [Group A] [Group D]

theorem cosetMap_equivariant (q : A →* D) (C : Subgroup A) (a : A) (x : A ⧸ C) :
    cosetMap q C (a • x) = q a • cosetMap q C x := by
  induction x using QuotientGroup.induction_on with
  | H x => simp only [MulAction.Quotient.smul_mk, smul_eq_mul, cosetMap_mk, map_mul]

theorem cosetMap_out (q : A →* D) (C : Subgroup A) (x : A ⧸ C) :
    cosetMap q C x = QuotientGroup.mk (q x.out) := by
  rw [← cosetMap_mk, QuotientGroup.out_eq']

/-- A retract is separable on any finite set of cosets. The two observations
(p, p ∘ r) implement the source's diagonal separation argument exactly. -/
theorem retract_coset_finite_separation [Group.ResiduallyFinite A]
    (C : Subgroup A) (r : A →* A) (hr : ∀ a, r a ∈ C)
    (hfix : ∀ c ∈ C, r c = c) (s : Finset (A ⧸ C)) :
    ∃ (D : Type u) (_ : Group D) (_ : Finite D) (q : A →* D),
      Set.InjOn (cosetMap q C) (s : Set (A ⧸ C)) := by
  classical
  let t := (s ×ˢ s).image (fun z => z.1.out⁻¹ * z.2.out)
  obtain ⟨H, hH⟩ := finite_set_quotient_injective (t ∪ t.image r)
  let p := QuotientGroup.mk' H.toSubgroup
  let q := p.prod (p.comp r)
  refine ⟨(A ⧸ H.toSubgroup) × (A ⧸ H.toSubgroup), inferInstance, inferInstance, q, ?_⟩
  intro x hx y hy he
  rw [cosetMap_out, cosetMap_out] at he
  have hm : q (x.out⁻¹ * y.out) ∈ C.map q := by
    simpa only [map_mul, map_inv] using QuotientGroup.eq.mp he
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hm
  have hp : p (x.out⁻¹ * y.out) = p (r (x.out⁻¹ * y.out)) := by
    have hleft := congrArg Prod.fst hce
    have hright := congrArg Prod.snd hce
    change p c = p (x.out⁻¹ * y.out) at hleft
    change p (r c) = p (r (x.out⁻¹ * y.out)) at hright
    rw [hfix c hc] at hright
    exact hleft.symm.trans hright
  have hd : x.out⁻¹ * y.out ∈ t :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  have hd' := hH (Finset.mem_union_left _ hd)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hd, rfl⟩)) hp
  have hmC : x.out⁻¹ * y.out ∈ C := hd' ▸ hr (x.out⁻¹ * y.out)
  have hxy : (QuotientGroup.mk x.out : A ⧸ C) = QuotientGroup.mk y.out :=
    QuotientGroup.eq.mpr hmC
  simpa only [QuotientGroup.out_eq'] using hxy

end RetractCosetSeparation

section RetractSemidirectSeparation

/-- Only the finitely many letters of a word must survive a map of alphabets. -/
theorem freeGroup_map_ne_one_of_injOn {X Y : Type*} [Nonempty X] [DecidableEq X]
    (f : X → Y) (w : FreeGroup X) (hw : w ≠ 1)
    (hf : Set.InjOn f {x | x ∈ w.toWord.map Prod.fst}) :
    FreeGroup.map f w ≠ 1 := by
  let g := Function.invFunOn f {x | x ∈ w.toWord.map Prod.fst}
  have hgf : FreeGroup.map g (FreeGroup.map f w) = w := by
    rw [FreeGroup.map.comp]
    have hm : (w.toWord.map fun a => ((g ∘ f) a.1, a.2)) = w.toWord := by
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro a ha
      have hx : a.1 ∈ w.toWord.map Prod.fst := List.mem_map.mpr ⟨a, ha, rfl⟩
      exact Prod.ext (hf.leftInvOn_invFunOn hx) rfl
    calc
      FreeGroup.map (g ∘ f) w = FreeGroup.map (g ∘ f) (FreeGroup.mk w.toWord) :=
        congrArg _ FreeGroup.mk_toWord.symm
      _ = FreeGroup.mk w.toWord := by rw [FreeGroup.map.mk, hm]
      _ = w := FreeGroup.mk_toWord
  intro he
  rw [he, map_one] at hgf
  exact hw hgf.symm

/-- The special permutational semidirect product used to add a graph-group
vertex is residually finite when the stabilizer is a retract. -/
theorem retract_semidirect_residuallyFinite {A : Type u} [Group A]
    [Group.ResiduallyFinite A] (C : Subgroup A) (r : A →* A)
    (hr : ∀ a, r a ∈ C) (hfix : ∀ c ∈ C, r c = c) :
    Group.ResiduallyFinite (FreeGroup (A ⧸ C) ⋊[freeAction A (A ⧸ C)] A) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro x hx
  by_cases ha : x.right = 1
  · have hw : x.left ≠ 1 := by
      intro he
      apply hx
      ext <;> assumption
    obtain ⟨D, hD, hfD, q, hq⟩ := retract_coset_finite_separation C r hr hfix
      (x.left.toWord.map Prod.fst).toFinset
    let : Group D := hD
    have : Finite D := hfD
    let f := FreeGroup.map (cosetMap q C)
    let Q := SemidirectProduct.map f q
      (freeAction_map_equivariant q (cosetMap q C) (cosetMap_equivariant q C))
    have := freeGroup_residuallyFinite (D ⧸ C.map q)
    have := finite_semidirect_residuallyFinite (freeAction D (D ⧸ C.map q))
    have hQ : Q x ≠ 1 := by
      intro he
      have hl : f x.left = 1 := congrArg SemidirectProduct.left he
      apply freeGroup_map_ne_one_of_injOn (cosetMap q C) x.left hw _ hl
      intro a ha b hb he
      exact hq (by simpa using ha) (by simpa using hb) he
    obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (Q x) hQ
    refine ⟨_, inferInstance, inferInstance, (QuotientGroup.mk' H.toSubgroup).comp Q, ?_⟩
    intro he
    exact hH ((QuotientGroup.eq_one_iff _).mp he)
  · obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem x.right ha
    refine ⟨_, inferInstance, inferInstance,
      (QuotientGroup.mk' H.toSubgroup).comp SemidirectProduct.rightHom, ?_⟩
    intro he
    exact hH ((QuotientGroup.eq_one_iff _).mp he)

end RetractSemidirectSeparation

section ArtinUniversal

variable {V W K : Type*} [Group K] (L : SimpleGraph V)

/-- Residual finiteness pulls back along an injective homomorphism. -/
theorem residuallyFinite_of_injective {G H : Type*} [Group G] [Group H]
    [Group.ResiduallyFinite H] (f : G →* H) (hf : Function.Injective f) :
    Group.ResiduallyFinite G := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hfg : f g ≠ 1 := fun h => hg (hf (h.trans (map_one f).symm))
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (f g) hfg
  refine ⟨_, inferInstance, inferInstance, (QuotientGroup.mk' N.toSubgroup).comp f, ?_⟩
  intro he
  exact hN ((QuotientGroup.eq_one_iff _).mp he)

end ArtinUniversal

section ArtinOption

variable {V : Type*} (L : SimpleGraph (Option V))

attribute [local instance] OAI.EilenbergGanea.instDecidableRelOptionAdj_solutions
theorem linkRetraction_mem (a : deletedGroup L) : linkRetraction L a ∈ linkSubgroup L := by
  classical
  apply PresentedGroup.generated_by (artinRelations (deletedGraph L))
    ((linkSubgroup L).comap (linkRetraction L)) _ a
  intro v
  change linkRetraction L (artinGenerator (deletedGraph L) v) ∈ linkSubgroup L
  rw [linkRetraction_generator]
  split_ifs with hv
  · exact Subgroup.subset_closure ⟨v, hv, rfl⟩
  · exact (linkSubgroup L).one_mem

theorem linkRetraction_fix (c : deletedGroup L) (hc : c ∈ linkSubgroup L) :
    linkRetraction L c = c := by
  classical
  have hle : linkSubgroup L ≤ (linkRetraction L).eqLocus (MonoidHom.id _) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, hv, rfl⟩
    change linkRetraction L (artinGenerator (deletedGraph L) v) = _
    simp [hv]
  exact hle hc

theorem optionForward_injective : Function.Injective (optionForward L) := by
  have he : (optionBackward L).comp (optionForward L) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro v
    cases v <;> simp [optionForward, optionBackward, optionGenerator, deletedInclusion, artinMap]
  exact (show Function.LeftInverse (optionBackward L) (optionForward L) from
    fun a => DFunLike.congr_fun he a).injective

end ArtinOption

/-- Graph groups on finite graphs are residually finite, by deletion of a
vertex and the retract-coset semidirect splitting. -/
theorem artin_residuallyFinite_oai (V : Type u) [Finite V] (L : SimpleGraph V) :
    Group.ResiduallyFinite (ArtinGroup L) := by
  classical
  apply Finite.induction_empty_option (P := fun W => ∀ M : SimpleGraph W,
    Group.ResiduallyFinite (ArtinGroup M)) _ _ _ V L
  · intro A B e hA M
    let N := M.comap e
    let f : ArtinGroup M →* ArtinGroup N :=
      artinMap M N e.symm (by intro v w h; simpa [N] using h)
    let g : ArtinGroup N →* ArtinGroup M := artinMap N M e (fun _ _ h => h)
    have hfg : g.comp f = MonoidHom.id _ := by
      apply PresentedGroup.ext
      intro v
      change g (f (artinGenerator M v)) = artinGenerator M v
      simp [g, f, artinMap]
    have := hA N
    apply residuallyFinite_of_injective f
    exact (show Function.LeftInverse g f from fun a => DFunLike.congr_fun hfg a).injective
  · intro M
    rw [Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
    intro a _
    have hm : a ∈ (⊥ : Subgroup (ArtinGroup M)) :=
      PresentedGroup.generated_by _ ⊥ (fun v => PEmpty.elim v) a
    exact hm
  · intro A _ hA M
    have := hA (deletedGraph M)
    have := retract_semidirect_residuallyFinite (linkSubgroup M) (linkRetraction M)
      (linkRetraction_mem M) (linkRetraction_fix M)
    exact residuallyFinite_of_injective (optionForward M) (optionForward_injective M)


end EilenbergGanea

end

end OAI
end

theorem solution.{u} : type_of% @OAI.EilenbergGanea.artin_residuallyFinite_oai.{u} := @OAI.EilenbergGanea.artin_residuallyFinite_oai.{u}
