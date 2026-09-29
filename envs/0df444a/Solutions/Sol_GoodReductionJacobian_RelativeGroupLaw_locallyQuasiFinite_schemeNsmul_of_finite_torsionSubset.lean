-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7262b7ba-0207-5791-9008-28faecd2bcc3

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mWs11LT

theorem finite_of_finite_sections {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (hfin : {σ : Spec (CommRingCat.of K) ⟶ X | σ ≫ g = 𝟙 _}.Finite) : Finite X := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g

  have hsec : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ σ : Spec (CommRingCat.of K) ⟶ X, σ ≫ g = 𝟙 _ ∧ σ.base (IsLocalRing.closedPoint K) = x := by
    intro x hx
    refine ⟨Spec.map (residueFieldIsoBase g x hx).hom ≫ X.fromSpecResidueField x, ?_, ?_⟩
    · rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv g x hx, ← Spec.map_comp, Iso.inv_hom_id,
        Spec.map_id]
    · have hmem : (Spec.map (residueFieldIsoBase g x hx).hom ≫ X.fromSpecResidueField x).base
          (IsLocalRing.closedPoint K) ∈ Set.range (X.fromSpecResidueField x).base :=
        ⟨(Spec.map (residueFieldIsoBase g x hx).hom).base (IsLocalRing.closedPoint K), rfl⟩
      rw [Scheme.range_fromSpecResidueField] at hmem
      exact hmem

  have hcl : (closedPoints X).Finite := by
    haveI : Finite {σ : Spec (CommRingCat.of K) ⟶ X | σ ≫ g = 𝟙 _} := hfin
    let φ : closedPoints X → {σ : Spec (CommRingCat.of K) ⟶ X | σ ≫ g = 𝟙 _} := fun x =>
      ⟨(hsec x.1 (mem_closedPoints_iff.mp x.2)).choose, (hsec x.1 (mem_closedPoints_iff.mp x.2)).choose_spec.1⟩
    have hφ : Function.Injective φ := by
      intro x₁ x₂ h
      apply Subtype.ext
      rw [← (hsec x₁.1 (mem_closedPoints_iff.mp x₁.2)).choose_spec.2,
        ← (hsec x₂.1 (mem_closedPoints_iff.mp x₂.2)).choose_spec.2]
      exact congrArg (fun s : {σ : Spec (CommRingCat.of K) ⟶ X | σ ≫ g = 𝟙 _} =>
        (s.1).base (IsLocalRing.closedPoint K)) h
    exact Set.finite_coe_iff.mp (Finite.of_injective φ hφ)
  have hclosed : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hcl.isClosed_biUnion fun x hx => mem_closedPoints_iff.mp hx
  have huniv : (Set.univ : Set X) = closedPoints X := by
    have h := JacobsonSpace.closure_inter_closedPoints (X := X) (Z := Set.univ) isClosed_univ
    rw [Set.univ_inter, hclosed.closure_eq] at h
    exact h.symm
  have : (Set.univ : Set X).Finite := huniv ▸ hcl
  exact Set.finite_univ_iff.mp this

end P2mWs11LT

namespace P2mWs11LT

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem nsmul_coe (L : RelativeGroupLaw k f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (m : ℕ) (x : SchemeHomOver t f) : (L.nsmul t m x).1 = x.1 ≫ L.schemeNsmul m := by
  have hid : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (L.nsmul f m RelativeGroupLaw.idPoint)
      = L.nsmul t m (schemeHomOverComp x.1 x.2 RelativeGroupLaw.idPoint) :=
    L.nsmul_natural f t x.1 x.2 m RelativeGroupLaw.idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

theorem pow_eq_nsmul (L : RelativeGroupLaw k f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (m : ℕ) (x : SchemeHomOver t f) : (letI := L.pointGroup t; x ^ m) = L.nsmul t m x := by
  letI := L.pointGroup t
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, ih, L.nsmul_succ]; rfl

theorem finite_nsmul_eq (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (hfin : (L.torsionSubset t n).Finite) (y : SchemeHomOver t f) :
    {z : SchemeHomOver t f | L.nsmul t n z = y}.Finite := by
  by_cases hne : {z : SchemeHomOver t f | L.nsmul t n z = y}.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := hcomm t }
    have hz₀' : z₀ ^ n = y := by rw [pow_eq_nsmul]; exact hz₀
    apply Set.Finite.of_finite_image (f := fun z => z * z₀⁻¹)
    · apply hfin.subset
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ^ n = y := by rw [pow_eq_nsmul]; exact hz
      show L.IsTorsionPoint t n (z * z₀⁻¹)
      rw [RelativeGroupLaw.isTorsionPoint_def, ← pow_eq_nsmul]
      show (z * z₀⁻¹) ^ n = 1
      rw [mul_pow, inv_pow, hz', hz₀', mul_inv_cancel]
    · intro z₁ _ z₂ _ h
      exact mul_right_cancel h
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

theorem finite_sections_pullback (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (hfin : (L.torsionSubset t n).Finite) (y : SchemeHomOver t f) :
    {σ : T ⟶ pullback (L.schemeNsmul n) y.1 | σ ≫ pullback.snd (L.schemeNsmul n) y.1 = 𝟙 _}.Finite := by
  have hS := finite_nsmul_eq L hcomm t n hfin y
  let ψ : {σ : T ⟶ pullback (L.schemeNsmul n) y.1 | σ ≫ pullback.snd (L.schemeNsmul n) y.1 = 𝟙 _} →
      {z : SchemeHomOver t f | L.nsmul t n z = y} := fun σ =>
    ⟨⟨σ.1 ≫ pullback.fst (L.schemeNsmul n) y.1, by
        have h1 : pullback.fst (L.schemeNsmul n) y.1 ≫ f =
            (pullback.fst (L.schemeNsmul n) y.1 ≫ L.schemeNsmul n) ≫ f := by
          rw [Category.assoc, L.schemeNsmul_over n]
        rw [Category.assoc, h1, pullback.condition, Category.assoc, y.2, ← Category.assoc, σ.2,
          Category.id_comp]⟩, by
        apply Subtype.ext
        rw [nsmul_coe]
        show (σ.1 ≫ pullback.fst (L.schemeNsmul n) y.1) ≫ L.schemeNsmul n = y.1
        rw [Category.assoc, pullback.condition, ← Category.assoc, σ.2, Category.id_comp]⟩
  haveI : Finite {z : SchemeHomOver t f | L.nsmul t n z = y} := hS
  have hψ : Function.Injective ψ := by
    intro σ₁ σ₂ h
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg (fun z : {z : SchemeHomOver t f | L.nsmul t n z = y} => z.1.1) h
    · rw [σ₁.2, σ₂.2]
  exact Set.finite_coe_iff.mp (Finite.of_injective ψ hψ)

theorem quasiFiniteAt_of_isClosed [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (n : ℕ)
    (hfin : (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k K))) n).Finite)
    [LocallyOfFiniteType (L.schemeNsmul n)]
    (x : G) (hx : IsClosed ({x} : Set G)) : (L.schemeNsmul n).QuasiFiniteAt x := by
  set h := L.schemeNsmul n with hh
  haveI : JacobsonSpace (Spec (CommRingCat.of k)) := inferInstance
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f

  set y : G := h.base x with hy
  have hyc : IsClosed ({y} : Set G) := by
    have := Scheme.Hom.closePoints_subset_preimage_closedPoints h (mem_closedPoints_iff.mpr hx)
    exact mem_closedPoints_iff.mp this

  haveI : LocallyOfFiniteType (G.fromSpecResidueField y) := isClosed_singleton_iff_locallyOfFiniteType.mp hyc
  let φ : CommRingCat.of k ⟶ G.residueField y := Spec.preimage (G.fromSpecResidueField y ≫ f)
  have hφ : Spec.map φ = G.fromSpecResidueField y ≫ f := Spec.map_preimage _
  haveI : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra k (G.residueField y) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType k (G.residueField y) := hft
  haveI : Module.Finite k (G.residueField y) := finite_of_finite_type_of_isJacobsonRing k _
  haveI : Algebra.IsAlgebraic k (G.residueField y) := Algebra.IsAlgebraic.of_finite k _
  let emb : G.residueField y →ₐ[k] K := IsAlgClosed.lift

  let tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e : Spec (CommRingCat.of K) ⟶ Spec (G.residueField y) := Spec.map (CommRingCat.ofHom emb.toRingHom)
  have he : e ≫ Spec.map φ = tK := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    show emb.toRingHom.comp φ.hom = algebraMap k K
    exact emb.comp_algebraMap
  let ybar : SchemeHomOver tK f := ⟨e ≫ G.fromSpecResidueField y, by rw [Category.assoc, ← hφ, he]⟩

  let F' : Scheme.{u} := pullback h ybar.1
  haveI : LocallyOfFiniteType (pullback.snd h ybar.1) := inferInstance
  haveI hF' : Finite F' :=
    finite_of_finite_sections (pullback.snd h ybar.1) (finite_sections_pullback L hcomm tK n hfin ybar)

  let m : F' ⟶ h.fiber y :=
    pullback.lift (pullback.fst h ybar.1) (pullback.snd h ybar.1 ≫ e)
      (by rw [pullback.condition, Category.assoc])
  have hm_snd : m ≫ h.fiberToSpecResidueField y = pullback.snd h ybar.1 ≫ e := pullback.lift_snd _ _ _
  have hm_fst : m ≫ h.fiberι y = pullback.fst h ybar.1 := pullback.lift_fst _ _ _
  have hbig : IsPullback (m ≫ h.fiberι y) (pullback.snd h ybar.1) h (e ≫ G.fromSpecResidueField y) := by
    rw [hm_fst]
    exact IsPullback.of_hasPullback h ybar.1
  have hsq : IsPullback m (pullback.snd h ybar.1) (h.fiberToSpecResidueField y) e :=
    IsPullback.of_right hbig hm_snd (IsPullback.of_hasPullback h (G.fromSpecResidueField y))
  haveI : Surjective e := ⟨fun p => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  haveI : Surjective m := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip inferInstance
  haveI : Finite (h.fiber y) := Finite.of_surjective m.base m.surjective
  haveI : DiscreteTopology (h.fiber y) := inferInstance
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  exact isOpen_discrete _

theorem main [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (n : ℕ)
    (hfin : (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k K))) n).Finite) :
    LocallyQuasiFinite (L.schemeNsmul n) := by
  haveI : LocallyOfFiniteType (L.schemeNsmul n) := by
    haveI : LocallyOfFiniteType (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact AlgebraicGeometry.locallyOfFiniteType_of_comp (L.schemeNsmul n) f
  haveI : JacobsonSpace (Spec (CommRingCat.of k)) := inferInstance
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  have hsub : closedPoints G ⊆ ((L.schemeNsmul n).quasiFiniteLocus : Set G) := fun x hx =>
    Scheme.Hom.mem_quasiFiniteLocus.mpr
      (quasiFiniteAt_of_isClosed L hcomm K n hfin x (mem_closedPoints_iff.mp hx))
  have hZ : IsClosed (((L.schemeNsmul n).quasiFiniteLocus : Set G)ᶜ) :=
    ((L.schemeNsmul n).quasiFiniteLocus).isOpen.isClosed_compl
  have hempty : (((L.schemeNsmul n).quasiFiniteLocus : Set G)ᶜ) = ∅ := by
    rw [← JacobsonSpace.closure_inter_closedPoints hZ]
    have : ((L.schemeNsmul n).quasiFiniteLocus : Set G)ᶜ ∩ closedPoints G = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and,
        not_not]
      intro hz hzc
      exact hz (hsub hzc)
    rw [this, closure_empty]
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_top]
  exact Set.compl_empty_iff.mp hempty

end P2mWs11LT

theorem solution
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (n : ℕ)
    (hfin : (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k K))) n).Finite) :
    LocallyQuasiFinite (L.schemeNsmul n) :=
  P2mWs11LT.main L hcomm K n hfin

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset (solution)
