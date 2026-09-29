-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1cc71415-8cce-5324-8709-30f196b50824

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.FormalCoordinates schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointOfBase_coe RelativeGroupLaw.baseChange_mul RelativeGroupLaw.baseChange_one"
namespace KB3aAsm
p2m_open "GoodReductionJacobian"

noncomputable section

section Ring

variable {B B' : Type} [CommRing B] [CommRing B'] (ι : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))

abbrev ringMap : B →+* B' := (Spec.preimage ι).hom

theorem specMap_ringMap : Spec.map (CommRingCat.ofHom (ringMap ι)) = ι := by
  rw [ringMap, CommRingCat.ofHom_hom, Spec.map_preimage]

abbrev algebraOver (C : Type) [CommRing C] [Algebra B' C] : Algebra B C :=
  ((algebraMap B' C).comp (ringMap ι)).toAlgebra

theorem specOver_comp (C : Type) [CommRing C] [Algebra B' C] :
    Scheme.specOver (𝒪 := B') C ≫ ι = @Scheme.specOver B _ C _ (algebraOver ι C) := by
  conv_lhs => rw [← specMap_ringMap ι]
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] (φ : B →+* B') {C : Type} [CommRing C]
    [Algebra B C] [Algebra B' C] (h : (algebraMap B' C).comp φ = algebraMap B C)
    (n : ℕ) (P : MvPowerSeries σ B) (a : σ → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map φ P) a = MvFormalGroup.nilEval n P a := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, h]

theorem nilMul_map {g : ℕ} (F : MvFormalGroup g B) (φ : B →+* B') {C : Type} [CommRing C]
    [Algebra B C] [Algebra B' C] (h : (algebraMap B' C).comp φ = algebraMap B C)
    (n : ℕ) (s t : Fin g → C) :
    (F.map φ).nilMul n s t = F.nilMul n s t := by
  funext i
  exact nilEval_map φ h n (F.toPowerSeries i) (Sum.elim s t)

end Ring

section Law

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

theorem one_val_congr (L : RelativeGroupLaw B f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of B)}
    (e : t₁ = t₂) : (L.one t₁).1 = (L.one t₂).1 := by
  subst e; rfl

theorem mul_val_congr (L : RelativeGroupLaw B f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of B)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

end Law

section Restrict

variable {B B' : Type} [CommRing B] [CommRing B'] (ι : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {d : ℕ}

def restrict (θ : RelativeGroupLaw.FormalCoordinates f d) :
    RelativeGroupLaw.FormalCoordinates (RelativeGroupLaw.baseChangeStr ι f) d := fun C _ _ s =>
  RelativeGroupLaw.baseChangePointOfBase ι
    ⟨(@θ C _ (algebraOver ι C) s).1, by rw [specOver_comp]; exact (@θ C _ (algebraOver ι C) s).2⟩

theorem restrict_fst (θ : RelativeGroupLaw.FormalCoordinates f d) (C : Type) [CommRing C] [Algebra B' C]
    (s : Fin d → C) :
    (restrict ι θ C s).1 ≫ pullback.fst f ι = (@θ C _ (algebraOver ι C) s).1 :=
  pullback.lift_fst _ _ _

theorem restrict_snd (θ : RelativeGroupLaw.FormalCoordinates f d) (C : Type) [CommRing C] [Algebra B' C]
    (s : Fin d → C) :
    (restrict ι θ C s).1 ≫ pullback.snd f ι = Scheme.specOver (𝒪 := B') C :=
  (restrict ι θ C s).2

end Restrict

end

end GoodReductionJacobian.KB3aAsm

open GoodReductionJacobian.KB3aAsm in
theorem solution
    {B B' : Type} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f d) (hθ : L.IsFormalCoordinates F θ) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates (RelativeGroupLaw.baseChangeStr ι f) d,
      (L.baseChange ι).IsFormalCoordinates (F.map (Spec.preimage ι).hom) θ' ∧
      ∀ (C : Type) [CommRing C] [Algebra B' C] (s : Fin d → C),
        letI : Algebra B C := ((algebraMap B' C).comp (Spec.preimage ι).hom).toAlgebra
        (θ' C s).1 ≫ pullback.fst f ι = (θ C s).1 := by
  classical
  refine ⟨restrict ι θ, ⟨?_, ?_⟩, fun C _ _ s => restrict_fst ι θ C s⟩
  ·
    intro C _ _ C' _ _ ψ s hs
    letI iC : Algebra B C := algebraOver ι C
    letI iC' : Algebra B C' := algebraOver ι C'
    let ψB : C →ₐ[B] C' :=
      { ψ.toRingHom with
        commutes' := fun b => by
          show ψ (algebraMap B' C (ringMap ι b)) = algebraMap B' C' (ringMap ι b)
          exact ψ.commutes (ringMap ι b) }
    have hnat := congrArg Subtype.val (hθ.1 C C' ψB s hs)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, restrict_fst, restrict_fst]
      exact hnat
    · rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, restrict_snd, restrict_snd, Scheme.specMap_algHom_comp_specOver]
  · intro C _ _ J n hJ
    letI iC : Algebra B C := algebraOver ι C
    obtain ⟨hinto, hinj, hsurj, hhom⟩ := hθ.2 C J n hJ

    have hq : Scheme.specOver (𝒪 := B) (C ⧸ J) = Scheme.specOver (𝒪 := B') (C ⧸ J) ≫ ι := by
      rw [specOver_comp]
    have hone : (L.one (Scheme.specOver (𝒪 := B) (C ⧸ J))).1 =
        (L.one (Scheme.specOver (𝒪 := B') (C ⧸ J) ≫ ι)).1 := one_val_congr L hq
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro s hs
      have h1 := congrArg Subtype.val (hinto s hs)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
      show _ = RelativeGroupLaw.baseChangePointOfBase ι (L.one _)
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, restrict_fst, RelativeGroupLaw.baseChangePointOfBase_coe,
          pullback.lift_fst, ← hone]
        exact h1
      · rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, restrict_snd, RelativeGroupLaw.baseChangePointOfBase_coe,
          pullback.lift_snd, Scheme.specMap_algHom_comp_specOver]
    ·
      intro s t hs ht hst
      apply hinj s t hs ht
      apply Subtype.ext
      rw [← restrict_fst ι θ C s, ← restrict_fst ι θ C t, hst]
    ·
      intro P hP
      let Q : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f :=
        ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2, specOver_comp]⟩
      have hQ : L.IsInfinitesimal J Q := by
        have h1 := congrArg (fun R => R.1 ≫ pullback.fst f ι) hP
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at h1
        rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst, ← hone] at h1
        exact Subtype.ext h1
      obtain ⟨s, hs, hsQ⟩ := hsurj Q hQ
      refine ⟨s, hs, ?_⟩
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [restrict_fst, hsQ]
      · rw [restrict_snd, P.2]
    ·
      intro s t hs ht
      have hmap : (F.map (Spec.preimage ι).hom).nilMul n s t = F.nilMul n s t :=
        nilMul_map F (ringMap ι) rfl n s t
      rw [hmap, RelativeGroupLaw.baseChange_mul]
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [restrict_fst, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst, hhom s t hs ht]
        exact mul_val_congr L (specOver_comp ι C).symm _ _ _ _ (restrict_fst ι θ C s).symm (restrict_fst ι θ C t).symm
      · rw [restrict_snd, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange (solution)
