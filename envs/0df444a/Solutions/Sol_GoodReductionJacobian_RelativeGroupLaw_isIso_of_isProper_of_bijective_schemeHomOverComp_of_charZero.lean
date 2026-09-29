-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dd6ccccd-c8df-5606-b5c5-1e424d942c5b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace BijHomIsoSol

section Hom

variable {k : Type u} [Field k] {G H : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)}
  {h : H ⟶ Spec (CommRingCat.of k)} (LG : RelativeGroupLaw k g) (LH : RelativeGroupLaw k h)
  (p : SchemeHomOver g h)
  (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
    NeronModelInfra.schemeHomOverComp (LG.mul t x y) p =
      LH.mul t (NeronModelInfra.schemeHomOverComp x p) (NeronModelInfra.schemeHomOverComp y p))

include hp in
theorem comp_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (LG.one t) p = LH.one t := by
  letI := LH.pointGroup t
  have e : NeronModelInfra.schemeHomOverComp (LG.one t) p * NeronModelInfra.schemeHomOverComp (LG.one t) p =
      NeronModelInfra.schemeHomOverComp (LG.one t) p := by
    show LH.mul t _ _ = _
    rw [← hp, LG.one_mul]
  exact mul_right_cancel (e.trans (one_mul _).symm)

include hp in
theorem comp_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LG.inv t x) p = LH.inv t (NeronModelInfra.schemeHomOverComp x p) := by
  letI := LH.pointGroup t
  have e : NeronModelInfra.schemeHomOverComp (LG.inv t x) p * NeronModelInfra.schemeHomOverComp x p = 1 := by
    show LH.mul t _ _ = LH.one t
    rw [← hp, LG.inv_mul_cancel, comp_one LG LH p hp]
  exact eq_inv_of_mul_eq_one_left e

end Hom

section Algebra

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [CommRing A] [Algebra k A]

theorem exists_algHom_ker_eq [Module.Finite k A] (m : Ideal A) [m.IsMaximal] :
    ∃ ψ : A →ₐ[k] k, RingHom.ker ψ = m := by
  haveI : Module.Finite k (A ⧸ m) := inferInstance
  haveI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext x
  simp only [RingHom.mem_ker, AlgHom.coe_comp, AlgEquiv.coe_algHom, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem algebraMap_bijective_of_subsingleton_algHom [Module.Finite k A] [IsReduced A]
    (h1 : Subsingleton (A →ₐ[k] k)) (h2 : Nonempty (A →ₐ[k] k)) : Function.Bijective (algebraMap k A) := by
  obtain ⟨φ⟩ := h2
  haveI : Nontrivial A := φ.toRingHom.domain_nontrivial
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A

  haveI : IsLocalRing A := by
    apply IsLocalRing.of_unique_max_ideal
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    refine ⟨m, hm, fun m' hm' => ?_⟩
    obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (k := k) m
    obtain ⟨ψ', hψ'⟩ := exists_algHom_ker_eq (k := k) m'
    rw [← hψ, ← hψ', Subsingleton.elim ψ ψ']
  have hF : IsField A := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  haveI : IsDomain A := hF.isDomain
  haveI : Algebra.IsIntegral k A := Algebra.IsIntegral.of_finite k A
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Algebra

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)}
  (LG : RelativeGroupLaw k g) (hcG : LG.IsCommutative)
  {H : Scheme.{u}} {h : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType h] [IsReduced H]
  (LH : RelativeGroupLaw k h)
  (p : SchemeHomOver g h) [IsProper p.1]
  (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
    NeronModelInfra.schemeHomOverComp (LG.mul t x y) p =
      LH.mul t (NeronModelInfra.schemeHomOverComp x p) (NeronModelInfra.schemeHomOverComp y p))
  (hbij : Function.Bijective fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g =>
    NeronModelInfra.schemeHomOverComp x p)

local notation "S" => Spec (CommRingCat.of k)

include hcG hp hbij in
theorem main : IsIso p.1 := by
  classical

  have he : (LH.one (𝟙 S)).1 ≫ h = 𝟙 S := (LH.one (𝟙 S)).2
  haveI : IsClosedImmersion (LH.one (𝟙 S)).1 := isClosedImmersion_of_comp_eq_id (Y := S) h _ he
  let N : Scheme.{u} := pullback p.1 (LH.one (𝟙 S)).1
  let ιN : N ⟶ G := pullback.fst p.1 (LH.one (𝟙 S)).1
  let nS : N ⟶ S := pullback.snd p.1 (LH.one (𝟙 S)).1
  haveI : IsClosedImmersion ιN := inferInstance
  haveI : IsProper nS := inferInstance
  have hpg : p.1 ≫ h = g := p.2
  have hιg : ιN ≫ g = nS := by
    rw [← hpg, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]

  have one_eq : ∀ {T : Scheme.{u}} (t : T ⟶ S), (LH.one t).1 = t ≫ (LH.one (𝟙 S)).1 := by
    intro T t
    have := LH.one_natural (𝟙 S) t t (Category.comp_id t)
    exact (congrArg Subtype.val this).symm

  have factors_iff : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t g),
      (∃ P₀ : T ⟶ N, P₀ ≫ ιN = x.1) ↔ NeronModelInfra.schemeHomOverComp x p = LH.one t := by
    intro T t x
    constructor
    · rintro ⟨P₀, hP₀⟩
      apply Subtype.ext
      have ht : P₀ ≫ nS = t := by rw [← hιg, ← Category.assoc, hP₀]; exact x.2
      show x.1 ≫ p.1 = (LH.one t).1
      rw [one_eq, ← hP₀, Category.assoc, pullback.condition, ← Category.assoc, ht]
    · intro hx
      have hx' : x.1 ≫ p.1 = t ≫ (LH.one (𝟙 S)).1 := by rw [← one_eq]; exact congrArg Subtype.val hx
      exact ⟨pullback.lift x.1 t hx', pullback.lift_fst _ _ _⟩

  obtain ⟨x₀, hx₀⟩ := hbij.2 (LH.one (𝟙 S))
  have hN1 : Subsingleton (SchemeHomOver (𝟙 S) nS) := by
    refine ⟨fun a b => ?_⟩
    have ha : NeronModelInfra.schemeHomOverComp (⟨a.1 ≫ ιN, by rw [Category.assoc, hιg]; exact a.2⟩ :
        SchemeHomOver (𝟙 S) g) p = LH.one (𝟙 S) := (factors_iff (𝟙 S) _).mp ⟨a.1, rfl⟩
    have hb : NeronModelInfra.schemeHomOverComp (⟨b.1 ≫ ιN, by rw [Category.assoc, hιg]; exact b.2⟩ :
        SchemeHomOver (𝟙 S) g) p = LH.one (𝟙 S) := (factors_iff (𝟙 S) _).mp ⟨b.1, rfl⟩
    have := hbij.1 (ha.trans hb.symm)
    apply Subtype.ext
    rw [← cancel_mono ιN]
    exact congrArg Subtype.val this
  have hN2 : Nonempty (SchemeHomOver (𝟙 S) nS) := by
    obtain ⟨P₀, hP₀⟩ := (factors_iff (𝟙 S) x₀).mpr hx₀
    exact ⟨⟨P₀, by rw [← hιg, ← Category.assoc, hP₀]; exact x₀.2⟩⟩

  haveI : LocallyOfFiniteType nS := inferInstance
  haveI : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace (Y := S) nS
  have hclosed : (closedPoints N).Subsingleton := by
    intro a ha b hb
    have := congrArg (fun q => ((pointEquivClosedPoint nS) q).1)
      (hN1.elim ((pointEquivClosedPoint nS).symm ⟨a, ha⟩) ((pointEquivClosedPoint nS).symm ⟨b, hb⟩))
    simpa using this
  have hfin : (closedPoints N).Finite := hclosed.finite
  have hcl : closedPoints N = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints, closure_subset_iff_isClosed,
      ← (closedPoints N).biUnion_of_singleton]
    exact hfin.isClosed_biUnion fun _ ↦ id
  haveI : Finite N := Set.finite_univ_iff.mp (hcl ▸ hfin)
  haveI : LocallyQuasiFinite nS := .of_finite_preimage_singleton nS fun _ => Set.toFinite _
  haveI : IsFinite nS := IsFinite.of_isProper_of_locallyQuasiFinite nS
  haveI : IsFinite (ιN ≫ g) := by rw [hιg]; infer_instance

  have hone' : ∀ {T : Scheme.{u}} (t : T ⟶ S), ∃ P₀ : T ⟶ N, P₀ ≫ ιN = (LG.one t).1 := by
    intro T t
    exact (factors_iff t (LG.one t)).mpr (comp_one LG LH p hp t)
  have hmul' : ∀ {T : Scheme.{u}} (t : T ⟶ S) (P Q : SchemeHomOver t g),
      (∃ P₀ : T ⟶ N, P₀ ≫ ιN = P.1) → (∃ Q₀ : T ⟶ N, Q₀ ≫ ιN = Q.1) →
        (∃ R₀ : T ⟶ N, R₀ ≫ ιN = (LG.mul t P Q).1) ∧ (∃ S₀ : T ⟶ N, S₀ ≫ ιN = (LG.inv t P).1) := by
    intro T t P Q hP hQ
    rw [factors_iff] at hP hQ ⊢
    constructor
    · rw [hp, hP, hQ, LH.one_mul]
    · rw [factors_iff, comp_inv LG LH p hp, hP]
      letI := LH.pointGroup t
      exact inv_one
  obtain ⟨A, _, _, hAfin, -, j, e, hjiso, hjstr, -, hebij, -, -⟩ :=
    RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup LG
      (fun t x y => hcG t x y) ιN hone' hmul'
  haveI : Module.Finite k A := hAfin
  haveI : Algebra.FiniteType k A := inferInstance
  haveI : _root_.IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero k A

  have hs1 : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 S := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  have key : ∀ s : S ⟶ S, s = 𝟙 S →
      Subsingleton {P : SchemeHomOver s g // ∃ P₀ : S ⟶ N, P₀ ≫ ιN = P.1} ∧
        Nonempty {P : SchemeHomOver s g // ∃ P₀ : S ⟶ N, P₀ ≫ ιN = P.1} := by
    rintro s rfl
    refine ⟨⟨fun a b => Subtype.ext (hbij.1 ?_)⟩, ⟨⟨x₀, (factors_iff (𝟙 S) x₀).mpr hx₀⟩⟩⟩
    exact (((factors_iff (𝟙 S) a.1).mp a.2).trans ((factors_iff (𝟙 S) b.1).mp b.2).symm)
  obtain ⟨hsub, hne⟩ := key _ hs1
  have hA1 : Subsingleton (A →ₐ[k] k) := ⟨fun φ ψ =>
    WithConv.toConv_injective ((hebij k).1 (hsub.elim _ _))⟩
  have hA2 : Nonempty (A →ₐ[k] k) := by
    obtain ⟨P⟩ := hne
    obtain ⟨φ, -⟩ := (hebij k).2 P
    exact ⟨φ.ofConv⟩
  have hAk : Function.Bijective (algebraMap k A) := algebraMap_bijective_of_subsingleton_algHom hA1 hA2

  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    have : IsIso (CommRingCat.ofHom (algebraMap k A)) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact hAk
    infer_instance
  haveI : IsIso j := hjiso
  haveI : IsIso nS := by
    have e1 : j ≫ nS = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by rw [← hjstr, hιg]
    have e2 : nS = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
      rw [← e1, IsIso.inv_hom_id_assoc]
    rw [e2]
    infer_instance

  have ker_trivial : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp x p = LH.one t → x = LG.one t := by
    intro T t x hx
    obtain ⟨P₀, hP₀⟩ := (factors_iff t x).mpr hx
    obtain ⟨O₀, hO₀⟩ := hone' t
    have h1 : P₀ ≫ nS = t := by rw [← hιg, ← Category.assoc, hP₀]; exact x.2
    have h2 : O₀ ≫ nS = t := by rw [← hιg, ← Category.assoc, hO₀]; exact (LG.one t).2
    have h3 : P₀ = O₀ := by rw [← cancel_mono nS, h1, h2]
    apply Subtype.ext
    rw [← hP₀, h3, hO₀]
  haveI : Mono p.1 := by
    refine ⟨fun {T} a b hab => ?_⟩
    let t : T ⟶ S := a ≫ g
    let xa : SchemeHomOver t g := ⟨a, rfl⟩
    let xb : SchemeHomOver t g := ⟨b, by
      show b ≫ g = a ≫ g
      rw [← hpg, ← Category.assoc, ← hab, Category.assoc]⟩
    have hpx : NeronModelInfra.schemeHomOverComp xa p = NeronModelInfra.schemeHomOverComp xb p := Subtype.ext hab
    letI := LG.pointGroup t
    letI := LH.pointGroup t
    have hd : NeronModelInfra.schemeHomOverComp (xa * xb⁻¹) p = LH.one t := by
      show NeronModelInfra.schemeHomOverComp (LG.mul t xa (LG.inv t xb)) p = LH.one t
      rw [hp, comp_inv LG LH p hp, hpx]
      exact mul_inv_cancel _
    have := ker_trivial t _ hd
    have hab' : xa = xb := by
      have h' : xa * xb⁻¹ = 1 := this
      rw [← mul_inv_eq_one]
      exact h'
    exact congrArg Subtype.val hab'
  haveI : IsClosedImmersion p.1 := (IsClosedImmersion.iff_isProper_and_mono p.1).mpr ⟨inferInstance, inferInstance⟩

  haveI : JacobsonSpace H := LocallyOfFiniteType.jacobsonSpace (Y := S) h
  haveI : Surjective p.1 := by
    refine ⟨fun y => ?_⟩
    have hsub : closedPoints H ⊆ Set.range p.1 := by
      intro y hy
      obtain ⟨x, hx⟩ := hbij.2 ⟨pointOfClosedPoint h y hy, pointOfClosedPoint_comp h y hy⟩
      refine ⟨x.1 (IsLocalRing.closedPoint k), ?_⟩
      have hx' : x.1 ≫ p.1 = pointOfClosedPoint h y hy := congrArg Subtype.val hx
      rw [← Scheme.Hom.comp_apply, hx', pointOfClosedPoint_apply]
    have hrange : Set.range p.1 = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← closure_closedPoints (X := H)]
      exact closure_minimal hsub p.1.isClosedMap.isClosed_range
    exact (Set.eq_univ_iff_forall.mp hrange) y
  exact isIso_of_isClosedImmersion_of_surjective p.1

end Main

end BijHomIsoSol

end

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (LG : RelativeGroupLaw k g) (hcG : LG.IsCommutative)
    {H : Scheme.{u}} {h : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType h] [IsReduced H]
    (LH : RelativeGroupLaw k h)
    (p : SchemeHomOver g h) [IsProper p.1]
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) p =
        LH.mul t (NeronModelInfra.schemeHomOverComp x p) (NeronModelInfra.schemeHomOverComp y p))
    (hbij : Function.Bijective fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g =>
      NeronModelInfra.schemeHomOverComp x p) :
    IsIso p.1 :=
  BijHomIsoSol.main LG hcG LH p hp hbij

end S_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero (solution)
