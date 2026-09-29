-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_of_isFinite_endKerStr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/58c002d9-1feb-5d36-a364-06fdc823db8a

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mIsogFin

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

section Points

variable (L : RelativeGroupLaw K f)

theorem pull_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) (β : SchemeHomOver f f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (x ⊚ β) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) ⊚ β :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

theorem pull_one {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  L.one_natural t t' ψ hψ

theorem pull_inv {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h1 : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, pull_one]
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) *
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = 1 at h1
  exact eq_inv_of_mul_eq_one_left h1

variable {L}
variable {β : SchemeHomOver f f} (hβ : IsHom L β)
include hβ

theorem hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t) ⊚ β = L.one t := by
  letI := L.pointGroup t
  have h : (L.one t) ⊚ β = L.mul t ((L.one t) ⊚ β) ((L.one t) ⊚ β) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hβ t _ _
  change (L.one t) ⊚ β = ((L.one t) ⊚ β) * ((L.one t) ⊚ β) at h
  exact (mul_eq_left.mp h.symm)

theorem hom_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) :
    (L.inv t x) ⊚ β = L.inv t (x ⊚ β) := by
  letI := L.pointGroup t
  have h1 : L.mul t ((L.inv t x) ⊚ β) (x ⊚ β) = L.one t := by
    rw [← hβ, L.inv_mul_cancel, hom_one hβ]
  change ((L.inv t x) ⊚ β) * (x ⊚ β) = 1 at h1
  exact eq_inv_of_mul_eq_one_left h1

end Points

section Translate

variable (L : RelativeGroupLaw K f) {β : SchemeHomOver f f} (hβ : IsHom L β)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (ξ : SchemeHomOver t f)

abbrev P₀ : Scheme.{u} := pullback (L.endKerStr β) t

abbrev P₁ : Scheme.{u} := pullback β.1 (ξ.1 ≫ β.1)

abbrev t₀ : P₀ L t (β := β) ⟶ Spec (CommRingCat.of K) := pullback.snd (L.endKerStr β) t ≫ t

abbrev t₁ : P₁ t ξ (β := β) ⟶ Spec (CommRingCat.of K) := pullback.snd β.1 (ξ.1 ≫ β.1) ≫ t

def k₀ : SchemeHomOver (t₀ L t (β := β)) f :=
  ⟨pullback.fst (L.endKerStr β) t ≫ L.endKerι β, by
    rw [Category.assoc, RelativeGroupLaw.endKerι_comp_base, pullback.condition]⟩

def x₀ : SchemeHomOver (t₀ L t (β := β)) f :=
  ⟨pullback.snd (L.endKerStr β) t ≫ ξ.1, by rw [Category.assoc, ξ.2]⟩

def q₁ : SchemeHomOver (t₁ t ξ (β := β)) f :=
  ⟨pullback.fst β.1 (ξ.1 ≫ β.1), by
    have h : pullback.fst β.1 (ξ.1 ≫ β.1) ≫ f = pullback.fst β.1 (ξ.1 ≫ β.1) ≫ (β.1 ≫ f) := by
      rw [β.2]
    rw [h, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, β.2, ξ.2]⟩

def x₁ : SchemeHomOver (t₁ t ξ (β := β)) f :=
  ⟨pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1, by rw [Category.assoc, ξ.2]⟩

theorem k₀_comp : (k₀ L t (β := β)) ⊚ β = L.one (t₀ L t (β := β)) := by
  apply Subtype.ext
  change (pullback.fst (L.endKerStr β) t ≫ L.endKerι β) ≫ β.1 = (L.one _).1
  rw [one_coe L (t₀ L t)]
  change _ = (pullback.snd (L.endKerStr β) t ≫ t) ≫ _
  rw [Category.assoc, RelativeGroupLaw.endKerι_comp, ← Category.assoc, pullback.condition,
    Category.assoc]

theorem q₁_comp : (q₁ t ξ (β := β)) ⊚ β = (x₁ t ξ (β := β)) ⊚ β := by
  apply Subtype.ext
  change pullback.fst β.1 (ξ.1 ≫ β.1) ≫ β.1 = (pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1) ≫ β.1
  rw [pullback.condition, Category.assoc]

include hβ

def Φ : P₀ L t (β := β) ⟶ P₁ t ξ (β := β) :=
  pullback.lift (L.mul _ (k₀ L t) (x₀ L t ξ)).1 (pullback.snd (L.endKerStr β) t) (by
    have h : (L.mul _ (k₀ L t (β := β)) (x₀ L t ξ)) ⊚ β = (x₀ L t ξ) ⊚ β := by
      rw [hβ, k₀_comp, L.one_mul]
    have h' := congrArg Subtype.val h
    change (L.mul _ (k₀ L t (β := β)) (x₀ L t ξ)).1 ≫ β.1 =
      (pullback.snd (L.endKerStr β) t ≫ ξ.1) ≫ β.1 at h'
    rw [h', Category.assoc])

@[reassoc (attr := simp)]
theorem Φ_fst : Φ L hβ t ξ ≫ pullback.fst β.1 (ξ.1 ≫ β.1) = (L.mul _ (k₀ L t) (x₀ L t ξ)).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Φ_snd : Φ L hβ t ξ ≫ pullback.snd β.1 (ξ.1 ≫ β.1) = pullback.snd (L.endKerStr β) t :=
  pullback.lift_snd _ _ _

def c : P₁ t ξ (β := β) ⟶ L.endKer β :=
  pullback.lift (L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ))).1 (t₁ t ξ (β := β)) (by
    have h : (L.mul _ (q₁ t ξ (β := β)) (L.inv _ (x₁ t ξ))) ⊚ β = L.one _ := by
      rw [hβ, hom_inv hβ, q₁_comp]
      letI := L.pointGroup (t₁ t ξ (β := β))
      change ((x₁ t ξ (β := β)) ⊚ β) * ((x₁ t ξ (β := β)) ⊚ β)⁻¹ = 1
      exact mul_inv_cancel _
    have h' := congrArg Subtype.val h
    change (L.mul _ (q₁ t ξ (β := β)) (L.inv _ (x₁ t ξ))).1 ≫ β.1 = (L.one _).1 at h'
    rw [h', one_coe L])

@[reassoc (attr := simp)]
theorem c_fst : c L hβ t ξ ≫ L.endKerι β = (L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ))).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem c_snd : c L hβ t ξ ≫ L.endKerStr β = t₁ t ξ (β := β) :=
  pullback.lift_snd _ _ _

def Ψ : P₁ t ξ (β := β) ⟶ P₀ L t (β := β) :=
  pullback.lift (c L hβ t ξ) (pullback.snd β.1 (ξ.1 ≫ β.1)) (by rw [c_snd])

@[reassoc (attr := simp)]
theorem Ψ_fst : Ψ L hβ t ξ ≫ pullback.fst (L.endKerStr β) t = c L hβ t ξ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Ψ_snd : Ψ L hβ t ξ ≫ pullback.snd (L.endKerStr β) t = pullback.snd β.1 (ξ.1 ≫ β.1) :=
  pullback.lift_snd _ _ _

theorem Ψ_t₀ : Ψ L hβ t ξ ≫ t₀ L t (β := β) = t₁ t ξ (β := β) := by
  rw [← Category.assoc, Ψ_snd]

theorem Ψ_pull_k₀ :
    GoodReductionJacobian.schemeHomOverComp (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (k₀ L t) =
      L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ)) := by
  apply Subtype.ext
  change Ψ L hβ t ξ ≫ (pullback.fst (L.endKerStr β) t ≫ L.endKerι β) = _
  rw [← Category.assoc, Ψ_fst, c_fst]

theorem Ψ_pull_x₀ :
    GoodReductionJacobian.schemeHomOverComp (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (x₀ L t ξ) = x₁ t ξ := by
  apply Subtype.ext
  change Ψ L hβ t ξ ≫ (pullback.snd (L.endKerStr β) t ≫ ξ.1) = pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1
  rw [← Category.assoc, Ψ_snd]

theorem Ψ_Φ : Ψ L hβ t ξ ≫ Φ L hβ t ξ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Φ_fst, Category.id_comp]
    have h := L.mul_natural _ _ (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (k₀ L t) (x₀ L t ξ)
    have h' := congrArg Subtype.val h
    change Ψ L hβ t ξ ≫ (L.mul _ (k₀ L t) (x₀ L t ξ)).1 = _ at h'
    rw [h', Ψ_pull_k₀, Ψ_pull_x₀]
    letI := L.pointGroup (t₁ t ξ (β := β))
    change ((q₁ t ξ (β := β)) * (x₁ t ξ (β := β))⁻¹ * (x₁ t ξ (β := β))).1 = _
    rw [inv_mul_cancel_right]
    rfl
  · rw [Category.assoc, Φ_snd, Ψ_snd, Category.id_comp]

theorem Φ_surjective : Function.Surjective (Φ L hβ t ξ) := by
  intro z
  refine ⟨Ψ L hβ t ξ z, ?_⟩
  rw [← Scheme.Hom.comp_apply, Ψ_Φ]
  rfl

theorem preimage_subset_range :
    β.1 ⁻¹' Set.range (ξ.1 ≫ β.1) =
      Set.range (Φ L hβ t ξ ≫ pullback.fst β.1 (ξ.1 ≫ β.1)) := by
  rw [← Scheme.Pullback.range_fst β.1 (ξ.1 ≫ β.1)]
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := Φ_surjective L hβ t ξ z
    exact ⟨w, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨Φ L hβ t ξ w, by rw [Scheme.Hom.comp_apply]⟩

omit hβ in

theorem finite_P₀ [IsFinite (L.endKerStr β)] [Finite T] : Finite (P₀ L t (β := β)) := by
  have h : (Set.univ : Set (P₀ L t (β := β))).Finite := by
    have h1 : (Set.univ : Set (P₀ L t (β := β))) =
        (pullback.snd (L.endKerStr β) t) ⁻¹' Set.univ := by rw [Set.preimage_univ]
    rw [h1]
    exact Set.finite_univ.preimage' fun b _ =>
      (pullback.snd (L.endKerStr β) t).finite_preimage_singleton b
  exact Set.finite_univ_iff.mp h

theorem finite_preimage [IsFinite (L.endKerStr β)] [Finite T] :
    (β.1 ⁻¹' Set.range (ξ.1 ≫ β.1)).Finite := by
  haveI := finite_P₀ L t (β := β)
  rw [preimage_subset_range L hβ t ξ]
  exact Set.finite_range _

end Translate

variable (L : RelativeGroupLaw K f) {β : SchemeHomOver f f} (hβ : IsHom L β)
include hβ

private theorem _root_.P2mIsogFin.finite_preimage_singleton [IsFinite (L.endKerStr β)] (y : A) : (β.1 ⁻¹' {y}).Finite := by
  by_cases hy : y ∈ Set.range β.1
  · obtain ⟨x, rfl⟩ := hy

    let ξ : SchemeHomOver (A.fromSpecResidueField x ≫ f) f := ⟨A.fromSpecResidueField x, rfl⟩
    have h := finite_preimage L hβ (A.fromSpecResidueField x ≫ f) ξ
    have hr : Set.range (ξ.1 ≫ β.1) = {β.1 x} := by
      change Set.range (A.fromSpecResidueField x ≫ β.1) = _
      ext a
      constructor
      · rintro ⟨s, rfl⟩
        rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
        rfl
      · rintro rfl
        exact ⟨IsLocalRing.closedPoint (A.residueField x), by
          rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩
    rwa [hr] at h
  · have h : β.1 ⁻¹' {y} = ∅ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact hy ⟨a, rfl⟩
    rw [h]
    exact Set.finite_empty

p2m_export "P2mIsogFin" "finite_preimage_singleton"

theorem locallyQuasiFinite [LocallyOfFiniteType f] [IsFinite (L.endKerStr β)] :
    LocallyQuasiFinite β.1 := by
  haveI : LocallyOfFiniteType β.1 := by
    have : LocallyOfFiniteType (β.1 ≫ f) := by rw [β.2]; infer_instance
    exact locallyOfFiniteType_of_comp β.1 f
  exact LocallyQuasiFinite.of_finite_preimage_singleton β.1 (finite_preimage_singleton L hβ)

theorem isFinite [IsProper f] [IsFinite (L.endKerStr β)] : IsFinite β.1 := by
  haveI : IsProper β.1 := by
    have : IsProper (β.1 ≫ f) := by rw [β.2]; infer_instance
    exact IsProper.of_comp β.1 f
  haveI := locallyQuasiFinite L hβ
  exact IsFinite.of_isProper_of_locallyQuasiFinite β.1

end P2mIsogFin

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    (hβ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) β =
        L.mul t (NeronModelInfra.schemeHomOverComp x β) (NeronModelInfra.schemeHomOverComp y β))
    [IsFinite (L.endKerStr β)] :
    IsFinite β.1 :=
  P2mIsogFin.isFinite L (fun t x y => hβ t x y)

end

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr (solution)
