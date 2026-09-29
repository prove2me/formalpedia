-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_comp_pair_fibre_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/87b25c61-7fb2-5250-835f-95ca52b8fbc0

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel IsLocalRing"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.X DRLevel.toBase DRLevel.toBase0 DRLevel.fibre DRLevel.fibre0 DRLevel.fibreMap DRLevel.fibreMap0 IgusaScheme"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fibreMap fibreMap0"
namespace BCComp
p2m_open "ModularCurve.DRLevel ModularCurve"

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]
variable {κ₀ : Type} [Field κ₀] (toκ₀ : DRLevel.R q →+* κ₀) {κ : Type} [Field κ] (toκ : DRLevel.R q →+* κ)
  (e : κ₀ →+* κ) (he : e.comp toκ₀ = toκ)

abbrev b : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ₀) := Spec.map (CommRingCat.ofHom e)

omit [Fact q.Prime] in
include he in
theorem b_comp : b e ≫ Spec.map (CommRingCat.ofHom toκ₀) = Spec.map (CommRingCat.ofHom toκ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]

def E {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    pullback (pullback.snd f (Spec.map (CommRingCat.ofHom toκ₀))) (b e) ≅ pullback f (Spec.map (CommRingCat.ofHom toκ)) :=
  pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom toκ₀)) (b e) ≪≫ pullback.congrHom rfl (b_comp toκ₀ toκ e he)

@[reassoc (attr := simp)]
theorem E_hom_fst {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    (E toκ₀ toκ e he f).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [E, Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_fst, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_fst _ _ _

@[reassoc (attr := simp)]
theorem E_hom_snd {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    (E toκ₀ toκ e he f).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [E, Iso.trans_hom, pullback.congrHom_hom, Category.assoc, pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd _ _ _

@[reassoc (attr := simp)]
theorem E_inv_fst {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    (E toκ₀ toκ e he f).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [← E_hom_fst toκ₀ toκ e he f, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem E_inv_snd {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    (E toκ₀ toκ e he f).inv ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [← E_hom_snd toκ₀ toκ e he f, Iso.inv_hom_id_assoc]

omit [Fact q.Prime] in

theorem surjective_b : Surjective (b e) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of κ)))
  exact ⟨x, Subsingleton.elim _ _⟩

variable (N₀ q)

abbrev F := DRLevel.fibre (N₀ := N₀) toκ₀
abbrev F0 := DRLevel.fibre0 (N₀ := N₀) toκ₀
abbrev s : F N₀ q toκ₀ ⟶ Spec (CommRingCat.of κ₀) := pullback.snd _ _
abbrev s0 : F0 N₀ q toκ₀ ⟶ Spec (CommRingCat.of κ₀) := pullback.snd _ _

variable {N₀ q}
variable (c : F0 N₀ q toκ₀ ⟶ F N₀ q toκ₀) (hc : c ≫ s N₀ q toκ₀ = s0 N₀ q toκ₀)

def Qiso : pullback c (pullback.fst (s N₀ q toκ₀) (b e)) ≅ pullback (s0 N₀ q toκ₀) (b e) :=
  pullbackRightPullbackFstIso (s N₀ q toκ₀) (b e) c ≪≫ pullback.congrHom hc rfl

def cBC : pullback (s0 N₀ q toκ₀) (b e) ⟶ pullback (s N₀ q toκ₀) (b e) :=
  (Qiso toκ₀ e c hc).inv ≫ pullback.snd c (pullback.fst (s N₀ q toκ₀) (b e))

@[reassoc]
theorem cBC_snd : cBC toκ₀ e c hc ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [cBC, Qiso, Iso.trans_inv, pullback.congrHom_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem cBC_fst : cBC toκ₀ e c hc ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c := by
  simp only [cBC, Qiso, Iso.trans_inv, pullback.congrHom_inv, Category.assoc]
  rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, Category.comp_id]

scoped instance cBC_isClosedImmersion [IsClosedImmersion c] : IsClosedImmersion (cBC toκ₀ e c hc) := by
  unfold cBC
  haveI : IsClosedImmersion (pullback.snd c (pullback.fst (s N₀ q toκ₀) (b e))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  infer_instance

def comp' : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ :=
  (E toκ₀ toκ e he (DRLevel.toBase0 N₀ q)).inv ≫ cBC toκ₀ e c hc ≫ (E toκ₀ toκ e he (DRLevel.toBase N₀ q)).hom

def pr : DRLevel.fibre (N₀ := N₀) toκ ⟶ F N₀ q toκ₀ := (E toκ₀ toκ e he (DRLevel.toBase N₀ q)).inv ≫ pullback.fst _ _
def pr0 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ F0 N₀ q toκ₀ := (E toκ₀ toκ e he (DRLevel.toBase0 N₀ q)).inv ≫ pullback.fst _ _

theorem pr_fst : pr toκ₀ toκ e he ≫ pullback.fst _ _ = pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := by
  simp [pr]
theorem pr0_fst : pr0 toκ₀ toκ e he ≫ pullback.fst _ _ = pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := by
  simp [pr0]

scoped instance : Surjective (pr toκ₀ toκ e he (N₀ := N₀)) := by
  haveI := surjective_b e; unfold pr; infer_instance

theorem comp'_snd : comp' toκ₀ toκ e he c hc ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [comp', Category.assoc, E_hom_snd, cBC_snd, E_inv_snd]

theorem comp'_pr : comp' toκ₀ toκ e he c hc ≫ pr toκ₀ toκ e he = pr0 toκ₀ toκ e he ≫ c := by
  simp only [comp', pr, pr0, Category.assoc, Iso.hom_inv_id_assoc, cBC_fst]

scoped instance comp'_isClosedImmersion [IsClosedImmersion c] : IsClosedImmersion (comp' toκ₀ toκ e he c hc) := by
  unfold comp'; infer_instance

theorem exists_comp'_eq (x : F0 N₀ q toκ₀) (y' : DRLevel.fibre (N₀ := N₀) toκ) (h : c x = pr toκ₀ toκ e he y') :
    ∃ x' : DRLevel.fibre0 (N₀ := N₀) toκ, comp' toκ₀ toκ e he c hc x' = y' := by
  have h' : c x = (pullback.fst (s N₀ q toκ₀) (b e)) ((E toκ₀ toκ e he (DRLevel.toBase N₀ q)).inv y') := by
    rw [h]; rfl
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x _ h'
  refine ⟨(E toκ₀ toκ e he (DRLevel.toBase0 N₀ q)).hom ((Qiso toκ₀ e c hc).hom z), ?_⟩
  show ((Qiso toκ₀ e c hc).hom ≫ (E toκ₀ toκ e he (DRLevel.toBase0 N₀ q)).hom ≫ comp' toκ₀ toκ e he c hc) z = y'
  have hrw : (Qiso toκ₀ e c hc).hom ≫ (E toκ₀ toκ e he (DRLevel.toBase0 N₀ q)).hom ≫ comp' toκ₀ toκ e he c hc =
      pullback.snd c (pullback.fst (s N₀ q toκ₀) (b e)) ≫ (E toκ₀ toκ e he (DRLevel.toBase N₀ q)).hom := by
    simp only [comp', cBC, Iso.hom_inv_id_assoc, Category.assoc]
  rw [hrw, Scheme.Hom.comp_apply, hz2, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

theorem mem_range_comp'_iff (y' : DRLevel.fibre (N₀ := N₀) toκ) :
    y' ∈ Set.range (comp' toκ₀ toκ e he c hc) ↔ pr toκ₀ toκ e he y' ∈ Set.range c := by
  constructor
  · rintro ⟨x', rfl⟩
    refine ⟨pr0 toκ₀ toκ e he x', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← comp'_pr, Scheme.Hom.comp_apply]
  · rintro ⟨x, hx⟩
    exact exists_comp'_eq toκ₀ toκ e he c hc x y' hx

theorem comp'_fibreMap0 (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (hpi : c ≫ DRLevel.fibreMap0 π toκ₀ = 𝟙 _) :
    comp' toκ₀ toκ e he c hc ≫ DRLevel.fibreMap0 π toκ = 𝟙 _ := by
  apply pullback.hom_ext
  ·
    rw [Category.id_comp, Category.assoc]
    have h1 : DRLevel.fibreMap0 π toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 := pullback.lift_fst _ _ _
    have h0 : DRLevel.fibreMap0 π toκ₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 := pullback.lift_fst _ _ _
    rw [h1, ← pr_fst toκ₀ toκ e he, Category.assoc]
    rw [← Category.assoc (comp' _ _ _ _ _ _), comp'_pr, Category.assoc, ← h0, ← Category.assoc c, hpi, Category.id_comp,
      pr0_fst]
  · rw [Category.id_comp, Category.assoc]
    have h1 : DRLevel.fibreMap0 π toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
    rw [h1, Category.comp_id, comp'_snd]

theorem comp'_fibreMap (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (c₁ : F0 N₀ q toκ₀ ⟶ F N₀ q toκ₀) (hc₁ : c₁ ≫ s N₀ q toκ₀ = s0 N₀ q toκ₀)
    (hcw : c ≫ DRLevel.fibreMap w.hom hw toκ₀ = c₁) :
    comp' toκ₀ toκ e he c hc ≫ DRLevel.fibreMap w.hom hw toκ = comp' toκ₀ toκ e he c₁ hc₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    have h1 : DRLevel.fibreMap w.hom hw toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom := pullback.lift_fst _ _ _
    have h0 : DRLevel.fibreMap w.hom hw toκ₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom := pullback.lift_fst _ _ _
    rw [h1, ← pr_fst toκ₀ toκ e he, Category.assoc, ← Category.assoc (comp' _ _ _ _ _ _), comp'_pr, Category.assoc, ← h0,
      ← Category.assoc c, hcw, ← Category.assoc, ← comp'_pr toκ₀ toκ e he c₁ hc₁, Category.assoc]
  · rw [Category.assoc]
    have h1 : DRLevel.fibreMap w.hom hw toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
    rw [h1, Category.comp_id, comp'_snd, comp'_snd]

end ModularCurve.DRLevel.BCComp
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel.BCComp"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve"

open ModularCurve.DRLevel.BCComp in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (κ₀ : Type) [Field κ₀] (toκ₀ : DRLevel.R q →+* κ₀)
    (comp₀ : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ₀ ⟶ DRLevel.fibre (N₀ := N₀) toκ₀))
    (hover : ∀ i, comp₀ i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hci : ∀ i, IsClosedImmersion (comp₀ i))
    (hsurj : ∀ y : DRLevel.fibre (N₀ := N₀) toκ₀, y ∈ Set.range (comp₀ 0).base ∨ y ∈ Set.range (comp₀ 1).base)
    (hne : Set.range (comp₀ 0).base ≠ Set.range (comp₀ 1).base)
    (hpi : comp₀ 0 ≫ DRLevel.fibreMap0 π toκ₀ = 𝟙 _)
    (hcw : comp₀ 0 ≫ DRLevel.fibreMap w.hom hw toκ₀ = comp₀ 1)
    (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ) (φ : κ₀ →+* κ) (hφ : φ.comp toκ₀ = toκ) :
    ∃ comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _ ∧
      comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1 := by
  let e := φ
  let he := hφ
  let comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ) :=
    fun i => comp' toκ₀ toκ e he (comp₀ i) (hover i)
  have hrange : ∀ i (y' : DRLevel.fibre (N₀ := N₀) toκ),
      y' ∈ Set.range (comp i).base ↔ pr toκ₀ toκ e he y' ∈ Set.range (comp₀ i).base :=
    fun i y' => mem_range_comp'_iff toκ₀ toκ e he (comp₀ i) (hover i) y'
  refine ⟨comp, fun i => comp'_snd toκ₀ toκ e he _ _, fun i => ?_, fun y' => ?_, ?_, ?_, ?_⟩
  · haveI := hci i
    exact comp'_isClosedImmersion toκ₀ toκ e he (comp₀ i) (hover i)
  · rcases hsurj (pr toκ₀ toκ e he y') with h | h
    · exact Or.inl ((hrange 0 y').mpr h)
    · exact Or.inr ((hrange 1 y').mpr h)
  · intro heq
    apply hne
    have key : ∀ y : DRLevel.fibre (N₀ := N₀) toκ₀, y ∈ Set.range (comp₀ 0).base ↔ y ∈ Set.range (comp₀ 1).base := by
      intro y
      obtain ⟨y', rfl⟩ := (pr toκ₀ toκ e he).surjective y
      rw [← hrange 0 y', ← hrange 1 y', heq]
    exact Set.ext key
  · exact comp'_fibreMap0 toκ₀ toκ e he (comp₀ 0) (hover 0) π hpi
  · exact comp'_fibreMap toκ₀ toκ e he (comp₀ 0) (hover 0) w hw (comp₀ 1) (hover 1) hcw
end
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.ModularCurve.DRLevel.BCComp"

end S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom (solution)
