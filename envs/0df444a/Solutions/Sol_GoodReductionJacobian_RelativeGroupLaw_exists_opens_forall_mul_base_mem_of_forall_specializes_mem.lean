-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cf16814f-06fc-5536-b8e0-fd1eed4c357c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Topology

universe u

namespace P2mGoodTranslatorSol

variable {R : Type u} [CommRing R]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

noncomputable def rightMul {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ B :=
  (LB.mul (pullback.snd g t₀ ≫ t₀) ⟨pullback.fst g t₀, pullback.condition⟩
      (schemeHomOverComp (pullback.snd g t₀) rfl σ)).1

noncomputable def leftMul {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ B :=
  (LB.mul (pullback.snd g t₀ ≫ t₀) (schemeHomOverComp (pullback.snd g t₀) rfl γ)
      ⟨pullback.fst g t₀, pullback.condition⟩).1

theorem leftMul_comp_base {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) : leftMul LB t₀ γ ≫ g = pullback.snd g t₀ ≫ t₀ :=
  (LB.mul _ _ _).2

theorem rightMul_comp_base {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightMul LB t₀ σ ≫ g = pullback.snd g t₀ ≫ t₀ :=
  (LB.mul _ _ _).2

theorem comp_leftMul {T₀ T : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) (ψ : T ⟶ pullback g t₀) (t' : T ⟶ Spec (CommRingCat.of R))
    (hψ : ψ ≫ (pullback.snd g t₀ ≫ t₀) = t') :
    ψ ≫ leftMul LB t₀ γ =
      (LB.mul t' ⟨ψ ≫ pullback.snd g t₀ ≫ γ.1, by rw [Category.assoc, Category.assoc, γ.2, ← Category.assoc, ← hψ, Category.assoc]⟩
        ⟨ψ ≫ pullback.fst g t₀, by rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ, Category.assoc]⟩).1 := by
  have h := LB.mul_natural (pullback.snd g t₀ ≫ t₀) t' ψ hψ
    (schemeHomOverComp (pullback.snd g t₀) rfl γ) ⟨pullback.fst g t₀, pullback.condition⟩
  have h1 := congrArg Subtype.val h
  simp only [schemeHomOverComp_coe] at h1
  unfold leftMul
  rw [h1]
  congr 2

theorem comp_rightMul {T₀ T : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) (ψ : T ⟶ pullback g t₀) (t' : T ⟶ Spec (CommRingCat.of R))
    (hψ : ψ ≫ (pullback.snd g t₀ ≫ t₀) = t') :
    ψ ≫ rightMul LB t₀ σ =
      (LB.mul t' ⟨ψ ≫ pullback.fst g t₀, by rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ, Category.assoc]⟩
        ⟨ψ ≫ pullback.snd g t₀ ≫ σ.1, by rw [Category.assoc, Category.assoc, σ.2, ← Category.assoc, ← hψ, Category.assoc]⟩).1 := by
  have h := LB.mul_natural (pullback.snd g t₀ ≫ t₀) t' ψ hψ
    ⟨pullback.fst g t₀, pullback.condition⟩ (schemeHomOverComp (pullback.snd g t₀) rfl σ)
  have h1 := congrArg Subtype.val h
  simp only [schemeHomOverComp_coe] at h1
  unfold rightMul
  rw [h1]
  congr 2

section Main

variable [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g]

def badSet (U : B.Opens) (s₀ : B) : Set B :=
  (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
    ((rightMul LB (B.fromSpecResidueField s₀ ≫ g) ⟨B.fromSpecResidueField s₀, rfl⟩).base ⁻¹' ((U : Set B)ᶜ))

theorem not_mem_closure_badSet (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure (badSet LB U s₀) :=
  GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    LB U hU s₀ hs₀ η hηk hηmax

theorem specializes_fiberι_iff (y : ↑(Spec (CommRingCat.of R))) (a b : ↑(g.fiber y)) :
    (g.fiberι y).base a ⤳ (g.fiberι y).base b ↔ a ⤳ b :=
  (g.fiberι y).isEmbedding.isInducing.specializes_iff

theorem mem_range_fiberι_of_eq (y : ↑(Spec (CommRingCat.of R))) (b : B) (hb : g.base b = y) :
    ∃ b' : ↑(g.fiber y), (g.fiberι y).base b' = b := by
  have : b ∈ Set.range (g.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hb
  exact this

theorem base_fiberι (y : ↑(Spec (CommRingCat.of R))) (a : ↑(g.fiber y)) : g.base ((g.fiberι y).base a) = y := by
  have : (g.fiberι y).base a ∈ g ⁻¹' {y} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨a, rfl⟩
  exact this

theorem exists_specializes_closedInFibre (s : B) :
    ∃ s₀ : B, s ⤳ s₀ ∧ ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀ := by
  let F := g.fiber (g.base s)
  let s' : ↑F := g.asFiber s
  have hs' : (g.fiberι _).base s' = s := g.fiberι_asFiber s
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints (X := ↑F) (Z := closure {s'})
    ⟨s', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  refine ⟨(g.fiberι _).base c, ?_, ?_⟩
  · have h := (specializes_fiberι_iff (g := g) _ s' c).mpr (specializes_iff_mem_closure.mpr hc)
    rwa [hs'] at h
  · intro y hy hgy
    rw [base_fiberι] at hgy
    obtain ⟨y', rfl⟩ := mem_range_fiberι_of_eq (g := g) _ y hgy
    rw [specializes_fiberι_iff] at hy
    have hc' : IsClosed ({c} : Set ↑F) := hcc
    have : y' ∈ ({c} : Set ↑F) := hy.mem_closed hc' rfl
    rw [Set.mem_singleton_iff.mp this]

include LB in

theorem exists_maximal_specialFibre :
    ∃ η : B, g.base η = IsLocalRing.closedPoint R ∧
      ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η := by

  let e : Spec (CommRingCat.of R) ⟶ B := (LB.one (𝟙 _)).1
  have he : e ≫ g = 𝟙 _ := (LB.one (𝟙 _)).2
  let p : B := e.base (IsLocalRing.closedPoint R)
  have hp : g.base p = IsLocalRing.closedPoint R := by
    show (e ≫ g) (IsLocalRing.closedPoint R) = _
    rw [he]; rfl
  let F := g.fiber (IsLocalRing.closedPoint R)
  obtain ⟨p', hp'⟩ := mem_range_fiberι_of_eq (g := g) _ p hp
  let C : Set ↑F := irreducibleComponent p'
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_irreducibleComponent
  let c : ↑F := hC.genericPoint
  have hc : IsGenericPoint c C := hC.isGenericPoint_genericPoint hCcl
  refine ⟨(g.fiberι _).base c, base_fiberι _ _, ?_⟩
  intro y hy hgy
  obtain ⟨y', rfl⟩ := mem_range_fiberι_of_eq (g := g) _ y hgy
  rw [specializes_fiberι_iff] at hy

  have h1 : C ⊆ closure {y'} := by
    rw [← hc.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy)) isClosed_closure
  have h2 : closure {y'} = C := eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h1
  have hy' : IsGenericPoint y' C := by rw [← h2]; exact isGenericPoint_closure
  congr 1
  exact hy'.eq hc

theorem main (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U := by
  classical
  choose sp hsp₁ hsp₂ using (exists_specializes_closedInFibre (g := g))
  let Zc : Set B := ⋃ s ∈ (S : Set B), closure (badSet LB U (sp s))
  have hZc : IsClosed Zc := S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
  refine ⟨⟨Zcᶜ, hZc.isOpen_compl⟩, ?_, ?_⟩
  · obtain ⟨η, hηk, hηmax⟩ := exists_maximal_specialFibre LB
    refine ⟨η, ?_, hηk⟩
    show η ∈ Zcᶜ
    intro hη
    obtain ⟨s, hs, hηs⟩ := Set.mem_iUnion₂.mp hη
    exact not_mem_closure_badSet LB U hU (sp s) (hsp₂ s) η hηk hηmax hηs
  · intro z hz hzk R' _ _ _ _ _ γ hγ hγz K _ x t hx hxS
    replace hz : z ∈ Zcᶜ := hz
    by_contra hbad
    set s' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R R')) with hs'
    let γ' : SchemeHomOver s' g := ⟨γ, hγ⟩
    let τ : pullback g s' ⟶ B := leftMul LB s' γ'

    let κ₁ : Spec (CommRingCat.of K) ⟶ pullback g s' := pullback.lift x t hx
    have e1 : (LB.mul (t ≫ s') (schemeHomOverComp t rfl γ') ⟨x, hx⟩).1 = κ₁ ≫ τ := by
      rw [comp_leftMul LB s' γ' κ₁ (t ≫ s') (by rw [← Category.assoc, pullback.lift_snd])]
      congr 2
      · apply Subtype.ext
        simp only [schemeHomOverComp_coe, κ₁, pullback.lift_snd_assoc]
      · apply Subtype.ext
        simp only [κ₁, pullback.lift_fst]
    set b₁ : ↑(pullback g s') := κ₁.base (IsLocalRing.closedPoint K) with hb₁
    have hτb₁ : τ.base b₁ ∉ (U : Set B) := by
      intro h; apply hbad
      rw [e1, Scheme.Hom.comp_base, TopCat.comp_app]; exact h
    set s : B := x.base (IsLocalRing.closedPoint K) with hsdef
    have hp₁b₁ : (pullback.fst g s').base b₁ = s := by
      rw [hb₁, ← TopCat.comp_app, ← Scheme.Hom.comp_base, pullback.lift_fst]

    obtain ⟨b₀, hb₁b₀, hb₀s⟩ : ∃ b₀ : ↑(pullback g s'), b₁ ⤳ b₀ ∧ (pullback.fst g s').base b₀ = sp s := by
      have hfin : IsFinite s' := by
        rw [hs', IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
        infer_instance
      have hcl : IsClosed ((pullback.fst g s').base '' closure {b₁}) :=
        (pullback.fst g s').isClosedMap _ isClosed_closure
      have hmem : sp s ∈ (pullback.fst g s').base '' closure {b₁} := by
        have h1 : closure {s} ⊆ (pullback.fst g s').base '' closure {b₁} :=
          closure_minimal (Set.singleton_subset_iff.mpr ⟨b₁, subset_closure rfl, hp₁b₁⟩) hcl
        exact h1 ((specializes_iff_mem_closure).mp (hsp₁ s))
      obtain ⟨b₀, hb₀, e⟩ := hmem
      exact ⟨b₀, specializes_iff_mem_closure.mpr hb₀, e⟩
    have hτb₀ : τ.base b₀ ∉ (U : Set B) := fun h =>
      hτb₁ ((hb₁b₀.map τ.continuous).mem_open U.isOpen h)

    let κ₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ pullback g s' :=
      (pullback g s').fromSpecResidueField b₀
    let x₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B := κ₀ ≫ pullback.fst g s'
    have hx₀pt : x₀.base (IsLocalRing.closedPoint ((pullback g s').residueField b₀)) = sp s := by
      show (κ₀ ≫ pullback.fst g s') (IsLocalRing.closedPoint _) = sp s
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hb₀s]

    obtain ⟨u, hu⟩ : ∃ u : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ Spec (B.residueField (sp s)),
        u ≫ B.fromSpecResidueField (sp s) = x₀ := by
      refine ⟨Spec.map (B.descResidueField (Scheme.stalkClosedPointTo x₀)) ≫
        Spec.map (B.residueFieldCongr hx₀pt.symm).hom, ?_⟩
      rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
      exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ B x₀
    let γ₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B := κ₀ ≫ pullback.snd g s' ≫ γ
    have hbase : κ₀ ≫ (pullback.snd g s' ≫ s') = u ≫ (B.fromSpecResidueField (sp s) ≫ g) := by
      rw [← Category.assoc u, hu]; simp only [x₀, Category.assoc, pullback.condition]
    have hγ₀ : γ₀ ≫ g = u ≫ (B.fromSpecResidueField (sp s) ≫ g) := by
      rw [← hbase]; simp only [γ₀, Category.assoc, hγ]
    let q₁ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ pullback g (B.fromSpecResidueField (sp s) ≫ g) :=
      pullback.lift γ₀ u hγ₀
    have key : q₁ ≫ rightMul LB (B.fromSpecResidueField (sp s) ≫ g) ⟨B.fromSpecResidueField (sp s), rfl⟩ =
        κ₀ ≫ τ := by
      rw [comp_rightMul LB _ _ q₁ (κ₀ ≫ (pullback.snd g s' ≫ s'))
          (by rw [hbase]; simp only [q₁, pullback.lift_snd_assoc]),
        comp_leftMul LB s' γ' κ₀ (κ₀ ≫ (pullback.snd g s' ≫ s')) rfl]
      congr 2
      · apply Subtype.ext
        simp only [q₁, γ₀, γ', pullback.lift_fst]
      · apply Subtype.ext
        simp only [q₁, pullback.lift_snd_assoc, hu, x₀]
    have hq₁bad : (rightMul LB (B.fromSpecResidueField (sp s) ≫ g) ⟨B.fromSpecResidueField (sp s), rfl⟩).base
        (q₁.base (IsLocalRing.closedPoint _)) ∉ (U : Set B) := by
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, key, Scheme.Hom.comp_base, TopCat.comp_app]
      have : κ₀.base (IsLocalRing.closedPoint _) = b₀ := Scheme.fromSpecResidueField_apply b₀ _
      rw [this]; exact hτb₀
    have hD : γ.base ((pullback.snd g s').base b₀) ∈ badSet LB U (sp s) := by
      refine ⟨q₁.base (IsLocalRing.closedPoint _), hq₁bad, ?_⟩
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, pullback.lift_fst]
      show (κ₀ ≫ pullback.snd g s' ≫ γ) (IsLocalRing.closedPoint _) = γ ((pullback.snd g s') b₀)
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    have hbz : γ.base ((pullback.snd g s').base b₀) ⤳ z := by
      rw [← hγz]; exact (IsLocalRing.specializes_closedPoint _).map γ.continuous
    have hzC : z ∈ closure (badSet LB U (sp s)) := hbz.mem_closed isClosed_closure (subset_closure hD)
    exact hz (Set.mem_iUnion₂.mpr ⟨s, hxS, hzC⟩)

end Main

end P2mGoodTranslatorSol

open P2mGoodTranslatorSol in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U :=
  P2mGoodTranslatorSol.main LB U hU S

end S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem (solution)
