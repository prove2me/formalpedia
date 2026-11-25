-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_const_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:18.094222+00:00
-- url     : https://prove2.me/submissions/1df632b3-0f03-4038-9b25-b56721580d89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_comp
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_eq_zero_of_ev
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_lift
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply
import Theorems.Thm_GlobalTheory_FunDescent_exists_appTop_eq
import Theorems.Thm_GlobalTheory_ReducedSubgroup_exists_smooth_closed_subgroup
import Theorems.Thm_GlobalTheory_exists_isClosed_image_of_isClosed_subgroup
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k]
variable [IsAlgClosed k]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution {G B T N : Over (Sp k)} [GrpObj G] [GrpObj B] [GrpObj T]
    [GrpObj N] (i : T ⟶ G) (q : G ⟶ B) (ν : N ⟶ G) (i' : T ⟶ N) [IsMonHom q] [IsMonHom ν]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper B.hom] [Smooth T.hom]
    [Smooth N.hom] [QuasiCompact N.hom] [IsIntegral N.left] [IsClosedImmersion ν.left]
    (hk : IsPullback i (toUnit _) q η[B]) (hi : i' ≫ ν = i) (f : Γ(N.left, ⊤))
    (hf : ∀ (t : 𝟙_ (Over (Sp k)) ⟶ T) (y : 𝟙_ (Over (Sp k)) ⟶ N),
      ev ((t ≫ i') * y) f = ev y f) : ∃ r, const N r = f := by
  have : Mono ν := Over.mono_of_mono_left ν
  have hsat : ∀ {Z : Over (Sp k)} (g : Z ⟶ G) (n : Z ⟶ N), g ≫ q = n ≫ ν ≫ q →
      ∃ t : Z ⟶ T, ((t ≫ i') * n) ≫ ν = g := by
    intro Z g n e
    have w : (g * (n ≫ ν)⁻¹) ≫ q = toUnit Z ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, Category.assoc, mul_inv_cancel]
      rfl
    exact ⟨hk.lift _ _ w, by
      rw [MonObj.mul_comp, Category.assoc, hi, hk.lift_fst, inv_mul_cancel_right]⟩
  have hf' : ∀ {Z : Over (Sp k)} (t : Z ⟶ T) (n : Z ⟶ N),
      ((t ≫ i') * n).left.appTop.hom f = n.left.appTop.hom f := by
    intro Z t n
    have : Smooth (T ⊗ N).hom := inferInstanceAs (Smooth (pullback.fst T.hom N.hom ≫ T.hom))
    have : IsReduced (T ⊗ N).left := isReduced_of_smooth_of_isReduced (T ⊗ N).hom
    have h0 : ((fst T N ≫ i') * snd T N).left.appTop.hom f = (snd T N).left.appTop.hom f := by
      rw [← sub_eq_zero]
      refine eq_zero_of_ev fun x => ?_
      rw [map_sub, ← ev_comp, ← ev_comp, MonObj.comp_mul, ← Category.assoc, hf, sub_self]
    have h1 : (t ≫ i') * n = lift t n ≫ ((fst T N ≫ i') * snd T N) := by
      simp [MonObj.comp_mul]
    rw [h1, Over.comp_left, FunDescent.comp_appTop_apply, h0, ← FunDescent.comp_appTop_apply,
      ← Over.comp_left, lift_snd]
  obtain ⟨Z, hZ, hZ'⟩ := exists_isClosed_image_of_isClosed_subgroup k N B (ν ≫ q) inferInstance
    inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  let φ : (𝟙_ (Over (Sp k)) ⟶ N) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ ν ≫ q) fun x y => MonObj.mul_comp x y _
  obtain ⟨Y, _, β, -, hβ, hY, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k B
    inferInstance φ.range Z hZ fun y => by
      rw [← hZ']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
  have : IsReduced Y.left := isReduced_of_smooth_of_isReduced Y.hom
  obtain ⟨m, hm⟩ := exists_lift β (ν ≫ q) fun x => by
    rw [hr, ← hZ']
    exact ⟨x, trivial, rfl⟩
  let P : Over (Sp k) := Over.mk (pullback.snd q.left β.left ≫ Y.hom)
  let π : P ⟶ Y := Over.homMk (pullback.snd q.left β.left) rfl
  let p : P ⟶ G := Over.homMk (pullback.fst q.left β.left) (by
    change _ = pullback.snd q.left β.left ≫ Y.hom
    rw [← Over.w q, pullback.condition_assoc, Over.w])
  have hP : p ≫ q = π ≫ β := Over.OverMorphism.ext pullback.condition
  have : Smooth P.hom := inferInstanceAs (Smooth (pullback.snd q.left β.left ≫ Y.hom))
  have : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  obtain ⟨l, hl⟩ := exists_lift ν p fun x => by
    obtain ⟨n, -, hn⟩ := (hZ' (x ≫ π ≫ β)).2 (by
      rw [← hr]
      rintro _ ⟨a, rfl⟩
      exact ⟨(x ≫ π).left a, rfl⟩)
    obtain ⟨t, ht⟩ := hsat (x ≫ p) n (by rw [Category.assoc, hP, hn])
    rw [← ht]
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := FunDescent.exists_appTop_eq (pullback.snd q.left β.left)
    (l.left.appTop.hom f) fun W g₁ g₂ e => by
      let W' : Over (Sp k) := Over.mk (g₂ ≫ P.hom)
      let k₂ : W' ⟶ P := Over.homMk g₂ rfl
      let k₁ : W' ⟶ P := Over.homMk g₁ (by
        change g₁ ≫ pullback.snd q.left β.left ≫ Y.hom = g₂ ≫ pullback.snd q.left β.left ≫ Y.hom
        rw [reassoc_of% e])
      have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
      obtain ⟨t, ht⟩ := hsat ((k₁ ≫ l) ≫ ν) (k₂ ≫ l) (by
        simp only [Category.assoc, reassoc_of% hl, hP, reassoc_of% e'])
      have := hf' t (k₂ ≫ l)
      rw [(cancel_mono ν).1 ht] at this
      exact this
  let s : N ⟶ P := Over.homMk (pullback.lift ν.left m.left (congrArg (·.left) hm).symm) (by
    change _ ≫ pullback.snd q.left β.left ≫ Y.hom = _
    rw [pullback.lift_snd_assoc, Over.w])
  have hs : s ≫ l = 𝟙 N := by
    rw [← cancel_mono ν, Category.assoc, hl, Category.id_comp]
    exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hsm : s.left ≫ pullback.snd q.left β.left = m.left := pullback.lift_snd _ _ _
  have hfa : f = m.left.appTop.hom a := by
    rw [← hsm]
    erw [FunDescent.comp_appTop_apply, ha, ← FunDescent.comp_appTop_apply, ← Over.comp_left, hs]
    rfl
  have : IsProper Y.hom := by rw [← Over.w β]; infer_instance
  have hint : (const Y).IsIntegral :=
    RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
      (isIntegral_appTop_of_universallyClosed Y.hom)
  have hc : m.left.appTop.hom.comp (const Y) = const N := by
    ext r
    change m.left.appTop.hom (Y.hom.appTop.hom _) = _
    rw [← FunDescent.comp_appTop_apply, Over.w]
    rfl
  have hfi : (const N).IsIntegralElem f := by
    rw [hfa, ← hc]
    exact (hint a).map _
  letI := (const N).toAlgebra
  exact minpoly.mem_range_of_degree_eq_one k f (IsAlgClosed.degree_eq_one_of_irreducible k
    (minpoly.irreducible hfi))
end GlobalTheory.QuasiAffineTorus
