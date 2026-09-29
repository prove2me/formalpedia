-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_action_slice_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1f9e9ec1-9611-552e-9359-f259aec1325a

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) :
    ∃ σ : CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≅
        CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j =
        (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∧
      σ.hom ≫ (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) =
        CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j := by
  classical

  set m : CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f) ⟶ CategoryTheory.Limits.pullback (i ≫ f) f :=
    CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) with hm
  set a : CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f) ⟶ G := m ≫ L.action i with ha
  set iG : SchemeHomOver (i ≫ f) f := ⟨i, rfl⟩ with hiG

  have hm₁ : m ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) f = (pullback.fst (i ≫ f) (j ≫ f)) := by
    rw [hm, pullback.lift_fst, Category.comp_id]
  have hm₂ : m ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j := by
    rw [hm, pullback.lift_snd]
  have hP : (pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f := pullback.condition
  have haf : a ≫ f = (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f := by
    rw [ha, Category.assoc, L.action_over i, ← Category.assoc, hm₂, Category.assoc]
  have hR : (pullback.fst a j) ≫ a = (pullback.snd a j) ≫ j := pullback.condition
  have ht1 : (pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = (pullback.snd a j) ≫ j ≫ f := by
    rw [← haf, ← Category.assoc, hR, Category.assoc]
  have ht2 : ((pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = (pullback.snd a j) ≫ j ≫ f := by rw [Category.assoc, hP, ht1]

  have a_pt : ∀ {T : Scheme.{u}} (ψ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f))
      (t : T ⟶ Spec (CommRingCat.of k)) (ht : ψ ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = t)
      (h1 : (ψ ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = t) (h2 : (ψ ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j) ≫ f = t),
      ψ ≫ a = (L.mul t (NeronModelInfra.schemeHomOverComp (⟨ψ ≫ (pullback.fst (i ≫ f) (j ≫ f)), h1⟩ : SchemeHomOver t (i ≫ f)) iG)
        ⟨ψ ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j, h2⟩).1 := by
    intro T ψ t ht h1 h2
    have hψ : (ψ ≫ m) ≫ GoodReductionJacobian.RelativeGroupLaw.actionSource f i = t := by
      rw [GoodReductionJacobian.RelativeGroupLaw.actionSource, Category.assoc, ← Category.assoc m, hm₂,
        Category.assoc, ht]
    have := L.mul_natural _ t (ψ ≫ m) hψ (L.actionFstPoint i) (L.actionSndPoint i)
    rw [ha, ← Category.assoc]
    change (GoodReductionJacobian.schemeHomOverComp (ψ ≫ m) hψ
      (L.mul _ (L.actionFstPoint i) (L.actionSndPoint i))).1 = _
    rw [this]
    congr 2
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe, Category.assoc, hiG]
      rw [← Category.assoc m, hm₁]
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe,
        GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe]
      rw [Category.assoc, hm₂]

  have i_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      NeronModelInfra.schemeHomOverComp (LN.one t) iG = L.one t := by
    intro T t
    have h2 := hi t (LN.one t) (LN.one t)
    rw [LN.one_mul] at h2
    calc NeronModelInfra.schemeHomOverComp (LN.one t) iG
        = L.mul t (L.one t) (NeronModelInfra.schemeHomOverComp (LN.one t) iG) := (L.one_mul t _).symm
      _ = L.mul t (L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG) := by rw [L.inv_mul_cancel]
      _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (L.mul t (NeronModelInfra.schemeHomOverComp (LN.one t) iG)
              (NeronModelInfra.schemeHomOverComp (LN.one t) iG)) := by rw [L.mul_assoc]
      _ = L.mul t (L.inv t (NeronModelInfra.schemeHomOverComp (LN.one t) iG))
            (NeronModelInfra.schemeHomOverComp (LN.one t) iG) := by rw [← h2]
      _ = L.one t := L.inv_mul_cancel t _

  have inv_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (i ≫ f)),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x) =
        LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
    intro T T' t t' ψ hψ x
    have hyz : LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
        (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = LN.one t' := by
      rw [← LN.mul_natural t t' ψ hψ, LN.inv_mul_cancel, LN.one_natural]
    calc GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x)
        = LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x)) (LN.one t') :=
          (LN.mul_one t' _).symm
      _ = LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
            (LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
              (LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x))) := by rw [LN.mul_inv_cancel]
      _ = LN.mul t' (LN.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LN.inv t x))
            (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
            (LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by rw [LN.mul_assoc]
      _ = LN.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [hyz, LN.one_mul]

  have hE : L.mul ((pullback.snd a j) ≫ j ≫ f)
      (NeronModelInfra.schemeHomOverComp (⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) (i ≫ f)) iG)
      ⟨(pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j, by simp only [Category.assoc]; exact ht1⟩ =
      (⟨(pullback.snd a j) ≫ j, Category.assoc _ _ _⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) f) := by
    apply Subtype.ext
    change _ = (pullback.snd a j) ≫ j
    rw [← hR, a_pt (pullback.fst a j) ((pullback.snd a j) ≫ j ≫ f) ht1 ht2]

  have hinv2 : (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩).1 ≫ i ≫ f = (pullback.snd a j) ≫ j ≫ f :=
    (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩).2
  set σP : CategoryTheory.Limits.pullback a j ⟶ CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f) :=
    CategoryTheory.Limits.pullback.lift (f := i ≫ f) (g := j ≫ f)
      (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩).1 (pullback.snd a j) hinv2 with hσP
  have hσP₁ : σP ≫ (pullback.fst (i ≫ f) (j ≫ f)) = (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩).1 := by
    rw [hσP]; exact pullback.lift_fst _ _ _
  have hσP₂ : σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) = (pullback.snd a j) := by rw [hσP]; exact pullback.lift_snd _ _ _
  have hσPt : σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j ≫ f = (pullback.snd a j) ≫ j ≫ f := by rw [← Category.assoc, hσP₂]
  have hσP1' : (σP ≫ (pullback.fst (i ≫ f) (j ≫ f))) ≫ i ≫ f = (pullback.snd a j) ≫ j ≫ f := by rw [hσP₁]; exact hinv2
  have hσP2' : (σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j) ≫ f = (pullback.snd a j) ≫ j ≫ f := by rw [Category.assoc, Category.assoc, hσPt]
  have w2 : σP ≫ a = ((pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f))) ≫ j := by
    rw [a_pt σP ((pullback.snd a j) ≫ j ≫ f) hσPt hσP1' hσP2']
    have e1 : (NeronModelInfra.schemeHomOverComp (⟨σP ≫ (pullback.fst (i ≫ f) (j ≫ f)), hσP1'⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) (i ≫ f)) iG)
        = NeronModelInfra.schemeHomOverComp (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩) iG := by
      congr 1; exact Subtype.ext hσP₁
    have e2 : (⟨σP ≫ (pullback.snd (i ≫ f) (j ≫ f)) ≫ j, hσP2'⟩ : SchemeHomOver ((pullback.snd a j) ≫ j ≫ f) f) = ⟨(pullback.snd a j) ≫ j, Category.assoc _ _ _⟩ :=
      Subtype.ext (by simp only; rw [← Category.assoc, hσP₂])
    rw [e1, e2, ← hE, ← L.mul_assoc, ← hi, LN.inv_mul_cancel, i_one, L.one_mul]
    exact (Category.assoc _ _ _).symm
  set σ : CategoryTheory.Limits.pullback a j ⟶ CategoryTheory.Limits.pullback a j :=
    CategoryTheory.Limits.pullback.lift (f := a) (g := j) σP ((pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f))) w2 with hσ
  have hσ₁ : σ ≫ (pullback.fst a j) = σP := by rw [hσ]; exact pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ (pullback.snd a j) = (pullback.fst a j) ≫ (pullback.snd (i ≫ f) (j ≫ f)) := by rw [hσ]; exact pullback.lift_snd _ _ _
  have hσt : σ ≫ (pullback.snd a j) ≫ j ≫ f = (pullback.snd a j) ≫ j ≫ f := by rw [← Category.assoc, hσ₂, Category.assoc, ht1]

  have σσ : σ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, hσ₁]
      apply pullback.hom_ext
      · rw [Category.assoc, hσP₁]
        have := inv_natural ((pullback.snd a j) ≫ j ≫ f) ((pullback.snd a j) ≫ j ≫ f) σ hσt ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩
        have e3 : GoodReductionJacobian.schemeHomOverComp σ hσt (⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ : SchemeHomOver _ (i ≫ f)) =
            LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ :=
          Subtype.ext (by
            simp only [GoodReductionJacobian.schemeHomOverComp_coe]
            rw [← Category.assoc, hσ₁, hσP₁])
        rw [e3] at this
        have e4 : LN.inv ((pullback.snd a j) ≫ j ≫ f) (LN.inv ((pullback.snd a j) ≫ j ≫ f) ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩) = ⟨(pullback.fst a j) ≫ (pullback.fst (i ≫ f) (j ≫ f)), ht2⟩ := by
          letI := LN.pointGroup ((pullback.snd a j) ≫ j ≫ f); exact inv_inv _
        rw [e4] at this
        exact congrArg Subtype.val this
      · rw [Category.assoc, hσP₂, hσ₂]
    · rw [Category.id_comp, Category.assoc, hσ₂, ← Category.assoc, hσ₁, hσP₂]
  refine ⟨⟨σ, σ, σσ, σσ⟩, ?_, ?_⟩
  · exact hσ₂
  · rw [← Category.assoc, hσ₁, hσP₂]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap (solution)
