-- Prove2me | solution 1 for ModularCurve.IgusaScheme.subfieldClosure_range_germToFunctionField_union_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2eff2348-5b0e-59c9-9c13-1cd39982dc94

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite ModularCurve ModularCurve.IgusaScheme

noncomputable section

namespace IgusaChartDict

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S]

abbrev XS : Scheme.{0} := pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))

abbrev CS : Type := ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] S

noncomputable def gFin : Spec (CommRingCat.of (CS N ℓ S)) ⟶ XS N ℓ S :=
  (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) S).inv ≫
    pullback.map _ _ _ _ (ιFin N ℓ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ιFin_igusaTo]) (by rw [Category.comp_id, Category.id_comp])

scoped instance : IsOpenImmersion (gFin N ℓ S) := by
  unfold gFin; infer_instance

theorem gFin_fst : gFin N ℓ S ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιFin N ℓ := by
  unfold gFin
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

theorem gFin_snd : gFin N ℓ S ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(chartAlgFin N ℓ)) (B := S)).toRingHom) := by
  unfold gFin
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd, Category.comp_id]
  rfl

theorem range_gFin : Set.range (gFin N ℓ S).base =
    (pullback.fst (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).base ⁻¹' Set.range (ιFin N ℓ).base := by
  unfold gFin
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ,
    Scheme.Pullback.range_map]
  · simp
  · exact (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) S).inv.homeomorph.surjective

theorem opensRange_gFin : (gFin N ℓ S).opensRange =
    (pullback.fst (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))) ⁻¹ᵁ ((ιFin N ℓ) ''ᵁ ⊤) := by
  ext1
  rw [Scheme.Hom.coe_opensRange, range_gFin]
  simp

variable {N ℓ S}

abbrev UFin : (XS N ℓ S).Opens :=
  (pullback.fst (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))) ⁻¹ᵁ ((ιFin N ℓ) ''ᵁ ⊤)

theorem opensRange_gFin' : (gFin N ℓ S).opensRange = UFin (N := N) (ℓ := ℓ) (S := S) :=
  opensRange_gFin N ℓ S

theorem preimage_gFin_UFin : (gFin N ℓ S) ⁻¹ᵁ (UFin : (XS N ℓ S).Opens) = ⊤ := by
  rw [← opensRange_gFin', Scheme.Hom.preimage_opensRange]

scoped instance isIso_gFin_app : IsIso ((gFin N ℓ S).app UFin) :=
  Scheme.Hom.isIso_app _ _ (opensRange_gFin' (N := N) (ℓ := ℓ) (S := S)).ge

def αhom : CommRingCat.of ↥(chartAlgFin N ℓ) ⟶ Γ(XS N ℓ S, UFin) :=
  (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin N ℓ))).inv ≫ ((ιFin N ℓ).appIso ⊤).inv ≫
    (pullback.fst (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).app ((ιFin N ℓ) ''ᵁ ⊤)

def βhom : CommRingCat.of S ⟶ Γ(XS N ℓ S, UFin) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
    (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).appTop ≫
      (XS N ℓ S).presheaf.map (homOfLE le_top).op

def cmp : Γ(XS N ℓ S, UFin) ⟶ Γ(Spec (CommRingCat.of (CS N ℓ S)), ⊤) :=
  (gFin N ℓ S).appLE UFin ⊤ (preimage_gFin_UFin (N := N) (ℓ := ℓ) (S := S)).ge

scoped instance isIso_cmp : IsIso (cmp (N := N) (ℓ := ℓ) (S := S)) := by
  unfold cmp Scheme.Hom.appLE
  have : IsIso ((Spec (CommRingCat.of (CS N ℓ S))).presheaf.map
      (homOfLE (preimage_gFin_UFin (N := N) (ℓ := ℓ) (S := S)).ge).op) := by
    have h : (homOfLE (preimage_gFin_UFin (N := N) (ℓ := ℓ) (S := S)).ge) =
        eqToHom preimage_gFin_UFin.symm := Subsingleton.elim _ _
    rw [h, eqToHom_op]
    infer_instance
  infer_instance

theorem appLE_top_top {P Q : Scheme.{0}} (f : P ⟶ Q) (e : (⊤ : P.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE e) = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

theorem α_comm : αhom ≫ cmp (N := N) (ℓ := ℓ) (S := S) =
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).inv := by

  have key : ∀ (φ : Spec (CommRingCat.of (CS N ℓ S)) ⟶ ModularCurve.IgusaScheme N ℓ)
      (e : (⊤ : (Spec (CommRingCat.of (CS N ℓ S))).Opens) ≤ φ ⁻¹ᵁ ((ιFin N ℓ) ''ᵁ ⊤)),
      φ = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιFin N ℓ →
      (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin N ℓ))).inv ≫ ((ιFin N ℓ).appIso ⊤).inv ≫
        φ.appLE ((ιFin N ℓ) ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).inv := by
    intro φ e hφ
    subst hφ
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.appIso_inv_app_assoc, Scheme.Hom.map_appLE, appLE_top_top,
      ← Scheme.ΓSpecIso_inv_naturality]
  unfold αhom cmp
  simp only [Category.assoc]
  rw [← Scheme.Hom.comp_appLE]
  exact key _ _ (gFin_fst N ℓ S)

theorem β_comm : βhom ≫ cmp (N := N) (ℓ := ℓ) (S := S) =
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(chartAlgFin N ℓ)) (B := S)).toRingHom ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).inv := by
  have key : ∀ (φ : Spec (CommRingCat.of (CS N ℓ S)) ⟶ Spec (CommRingCat.of S))
      (e : (⊤ : (Spec (CommRingCat.of (CS N ℓ S))).Opens) ≤ φ ⁻¹ᵁ ⊤),
      φ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(chartAlgFin N ℓ)) (B := S)).toRingHom) →
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ φ.appLE ⊤ ⊤ e =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(chartAlgFin N ℓ)) (B := S)).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).inv := by
    intro φ e hφ
    subst hφ
    rw [appLE_top_top, ← Scheme.ΓSpecIso_inv_naturality]
  unfold βhom cmp
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE]
  erw [← Scheme.Hom.comp_appLE]
  exact key _ _ (gFin_snd N ℓ S)

theorem closure_range_α_β :
    Subring.closure (Set.range (αhom (N := N) (ℓ := ℓ) (S := S)) ∪ Set.range (βhom (N := N) (ℓ := ℓ) (S := S))) = ⊤ := by

  let e : Γ(XS N ℓ S, UFin) ≃+* CS N ℓ S :=
    ((asIso (cmp (N := N) (ℓ := ℓ) (S := S))) ≪≫ Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).commRingCatIsoToRingEquiv
  have he : ∀ z, e z = (Scheme.ΓSpecIso (CommRingCat.of (CS N ℓ S))).hom (cmp (N := N) (ℓ := ℓ) (S := S) z) := fun z => rfl
  have hα : ∀ a : ↥(chartAlgFin N ℓ), e (αhom a) = a ⊗ₜ 1 := by
    intro a
    rw [he, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Category.assoc, α_comm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  have hβ : ∀ b : S, e (βhom b) = 1 ⊗ₜ b := by
    intro b
    rw [he, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Category.assoc, β_comm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [eq_top_iff]
  intro z _

  have hmem : ∀ t : CS N ℓ S, e.symm t ∈ Subring.closure (Set.range (αhom (N := N) (ℓ := ℓ) (S := S)) ∪
      Set.range (βhom (N := N) (ℓ := ℓ) (S := S))) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | tmul a b =>
      have : a ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b = e (αhom a) * e (βhom b) := by
        rw [hα, hβ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, ← map_mul, RingEquiv.symm_apply_apply]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  simpa using hmem (e z)

theorem subfieldClosure_eq_top [IsIntegral (XS N ℓ S)] (x : XS N ℓ S)
    [Nonempty (Scheme.Opens.toScheme (UFin (N := N) (ℓ := ℓ) (S := S)))] :
    Subfield.closure
      (Set.range (fun a : ↥(chartAlgFin N ℓ) => (XS N ℓ S).germToFunctionField UFin (αhom a)) ∪
        Set.range (fun s : S =>
          algebraMap ((XS N ℓ S).presheaf.stalk x) (XS N ℓ S).functionField
            (((XS N ℓ S).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ := by
  have hU : IsAffineOpen (UFin : (XS N ℓ S).Opens) := by
    rw [← opensRange_gFin']; exact isAffineOpen_opensRange _
  haveI := functionField_isFractionRing_of_isAffineOpen (XS N ℓ S) UFin hU

  have hβgerm : ∀ s : S, (XS N ℓ S).germToFunctionField UFin (βhom s) =
      algebraMap ((XS N ℓ S).presheaf.stalk x) (XS N ℓ S).functionField
        (((XS N ℓ S).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))) := by
    have hmor : βhom ≫ (XS N ℓ S).germToFunctionField UFin =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).appTop ≫
            (XS N ℓ S).presheaf.germ ⊤ x trivial ≫
              (XS N ℓ S).presheaf.stalkSpecializes ((genericPoint_spec (XS N ℓ S)).specializes trivial) := by
      unfold βhom Scheme.germToFunctionField
      simp only [Category.assoc]
      rw [TopCat.Presheaf.germ_res, TopCat.Presheaf.germ_stalkSpecializes]
    intro s
    have h := CommRingCat.hom_ext_iff.mp hmor
    have h' := RingHom.congr_fun h s
    rw [RingHom.algebraMap_toAlgebra]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
    exact h'

  set M := Subfield.closure
      (Set.range (fun a : ↥(chartAlgFin N ℓ) => (XS N ℓ S).germToFunctionField UFin (αhom a)) ∪
        Set.range (fun s : S =>
          algebraMap ((XS N ℓ S).presheaf.stalk x) (XS N ℓ S).functionField
            (((XS N ℓ S).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) with hM
  have hgerm : ∀ z : Γ(XS N ℓ S, UFin), (XS N ℓ S).germToFunctionField UFin z ∈ M := by
    intro z
    have hz : z ∈ Subring.closure (Set.range (αhom (N := N) (ℓ := ℓ) (S := S)) ∪
        Set.range (βhom (N := N) (ℓ := ℓ) (S := S))) := by
      rw [closure_range_α_β]; trivial
    refine Subring.closure_induction (fun w hw => ?_) ?_ ?_ (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_)
      (fun a b _ _ ha hb => ?_) hz
    · rcases hw with ⟨a, rfl⟩ | ⟨s, rfl⟩
      · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      · rw [hβgerm]; exact Subfield.subset_closure (Or.inr ⟨s, rfl⟩)
    · rw [map_zero]; exact M.zero_mem
    · rw [map_one]; exact M.one_mem
    · rw [map_add]; exact M.add_mem ha hb
    · rw [map_neg]; exact M.neg_mem ha
    · rw [map_mul]; exact M.mul_mem ha hb

  rw [eq_top_iff]
  intro q _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(XS N ℓ S, UFin)) q
  exact M.div_mem (hgerm a) (hgerm b)

end IgusaChartDict
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top.IgusaChartDict"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top.IgusaChartDict"

open IgusaChartDict in

theorem solution
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (S : Type) [CommRing S] (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* S)
    [hint : IsIntegral (pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ)))]
    (x : ↥(pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)))] :
    Subfield.closure
      (Set.range (fun a : ↥(IgusaScheme.chartAlgFin N ℓ) =>
        ((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField ((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤))
            (((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).app ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin N ℓ).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N ℓ))).inv a))))) ∪
        Set.range (fun s : S =>
          algebraMap ((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk x) ↥((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).functionField)
            (((pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom ρ))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ := by
  letI : Algebra ↥(GaloisRep.ratLocalizedAt ℓ) S := ρ.toAlgebra
  exact IgusaChartDict.subfieldClosure_eq_top (N := N) (ℓ := ℓ) (S := S) x

end S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top (solution)
