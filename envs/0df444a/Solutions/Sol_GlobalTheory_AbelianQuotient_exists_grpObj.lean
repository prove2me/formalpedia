-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.exists_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:53.011804+00:00
-- url     : https://prove2.me/submissions/4ddf7496-4d2b-41b4-90c2-82805547b99d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Theorems.Thm_GlobalTheory_AbelianQuotient_exists_desc
import Theorems.Thm_GlobalTheory_AbelianQuotient_flat_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_surjective_tensorHom
import Theorems.Thm_GlobalTheory_AbelianQuotient_quasiCompact_tensorHom
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_tensorHom
import Theorems.Thm_GlobalTheory_FlatQuotient_exists_desc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}
namespace GlobalTheory.AbelianQuotient
theorem _root_.solution {A H Q : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H] (i : H ⟶ A)
    [IsMonHom i] (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q ∧ IsPullback i (toUnit H) q η[Q] := by
  have rel : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q ↔ ∃ t : W ⟶ H, a = (t ≫ i) * b := by
    intro W a b
    constructor
    · intro h
      refine ⟨hq.lift a b h ≫ fst H A, ?_⟩
      have h1 := hq.lift_fst a b h
      rw [comp_mul, hq.lift_snd] at h1
      rw [Category.assoc, h1]
    · rintro ⟨t, rfl⟩
      have := lift t b ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel (a ≫ fst A A) (b ≫ fst A A)).1 (by simpa using h =≫ fst Q Q)
    obtain ⟨t, ht⟩ := (rel (a ≫ snd A A) (b ≫ snd A A)).1 (by simpa using h =≫ snd Q Q)
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s * t, ?_⟩
    rw [MonObj.mul_eq_mul, comp_mul, comp_mul, hs, ht, mul_comp, _root_.mul_mul_mul_comm])
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel a b).1 h
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s⁻¹, ?_⟩
    rw [← Hom.inv_def, ← Hom.inv_def, hs, GrpObj.inv_comp, mul_inv])
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom, ?_⟩
  · rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
      IsCommMonObj.mul_comm_assoc]
  · have hk : IsPullback (lift (𝟙 H) (toUnit H ≫ η[A])) (toUnit H) (snd H A) η[A] := by
      refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst H A) ?_ ?_ ?_⟩⟩
      · intro s
        ext
        · simp
        · simp [s.condition, toUnit_unique (toUnit _) s.snd]
      · intro s
        exact toUnit_unique _ _
      · intro s l h1 _
        simp [← h1]
    have := hk.flip.paste_vert hq.flip
    have e : lift (𝟙 H) (toUnit H ≫ η[A]) ≫ ((fst H A ≫ i) * snd H A) = i := by
      simp [comp_mul, ← Hom.one_def]
    rw [e] at this
    exact this.flip
end GlobalTheory.AbelianQuotient
