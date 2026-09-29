-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.residue_baseGerm_surjective_and_isClosed_crossingPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/89bde616-70d1-57e5-8c3f-52196cd44156

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

universe u

noncomputable section

namespace ECL_CrossRat

private theorem residue_germ_surjective_of_field (K : Type u) [Field K] (pt : Spec (CommRingCat.of K)) :
    Function.Surjective fun k : K => IsLocalRing.residue ((Spec (CommRingCat.of K)).presheaf.stalk pt)
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ pt trivial ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k)) := by
  letI : Algebra (CommRingCat.of K) ((Spec (CommRingCat.of K)).presheaf.stalk pt) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of K) pt
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of K)).presheaf.stalk pt) pt.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of K) pt
  have hpt : pt.asIdeal = ⊥ := by
    haveI : pt.asIdeal.IsPrime := pt.isPrime
    exact Ideal.eq_bot_of_prime _
  have hbij : Function.Bijective (algebraMap (CommRingCat.of K) ((Spec (CommRingCat.of K)).presheaf.stalk pt)) := by
    refine IsField.localization_map_bijective (M := pt.asIdeal.primeCompl) ?_ (Field.toIsField K)
    intro h0
    exact h0 (by rw [hpt]; exact Ideal.zero_mem _)
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨k, rfl⟩ := hbij.2 w
  exact ⟨k, rfl⟩

private theorem residue_germ_surjective_and_isClosed {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (π : X ⟶ Spec (CommRingCat.of O))
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ X)
    (hs : s ≫ π = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :
    (Function.Surjective fun o : O => IsLocalRing.residue (X.presheaf.stalk (s.base (IsLocalRing.closedPoint _)))
      (X.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint _)) trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) ∧
    IsClosed ({s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))} : Set X) := by
  set k₀ := IsLocalRing.ResidueField O
  set pt : Spec (CommRingCat.of k₀) := IsLocalRing.closedPoint k₀
  set x := s.base pt
  constructor
  · intro z

    let w := s.residueFieldMap pt z
    obtain ⟨k, hk⟩ := residue_germ_surjective_of_field k₀ pt w
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective k
    refine ⟨o, (s.residueFieldMap pt).hom.injective ?_⟩
    change (X.residue x ≫ s.residueFieldMap pt) (X.presheaf.germ ⊤ x trivial (π.appTop _)) = w
    rw [Scheme.residue_residueFieldMap, CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap_apply]
    rw [← hk]
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    congr 2
    change (s.appTop (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) =
      (Scheme.ΓSpecIso (CommRingCat.of k₀)).inv (IsLocalRing.residue O o)
    rw [← CommRingCat.comp_apply _ s.appTop, ← Scheme.Hom.comp_appTop, hs]
    exact (congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))).symm
  ·
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let s' := pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp])
    have hsec : s' ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = 𝟙 _ := pullback.lift_snd _ _ _
    haveI : IsClosedImmersion s' := isClosedImmersion_of_comp_eq_id _ s' hsec
    haveI : IsClosedImmersion (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    have hs' : s = s' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    haveI : IsClosedImmersion s := by rw [hs']; infer_instance
    have hrange : Set.range s.base = {x} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨q, rfl⟩
        rw [Subsingleton.elim q pt]
      · rintro rfl; exact ⟨pt, rfl⟩
    rw [← hrange]
    exact s.isClosedEmbedding.isClosed_range

end ECL_CrossRat

end

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hinf : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hzero : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)
    (hrat : ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ XO (ΓM M H) hj ρO,
      s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
      s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) :
    (Function.Surjective fun o : O =>
      IsLocalRing.residue ((XO (ΓM M H) hj ρO).presheaf.stalk (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n)) (baseGerm ρO (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) o)) ∧
    IsClosed ({𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n} : Set ↥(XO (ΓM M H) hj ρO)) := by
  obtain ⟨s, hs1, hs2⟩ := hrat
  rw [← hs2]
  exact ECL_CrossRat.residue_germ_surjective_and_isClosed (XO.toBase (ΓM M H) hj ρO) s hs1

end S_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_residue_baseGerm_surjective_and_isClosed_crossingPt (solution)
