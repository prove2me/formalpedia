-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_local_lifts_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/91f15126-ad13-5159-9268-34107c54b4a2

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_local_lifts_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

set_option maxHeartbeats 3200000 in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)

    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)

    (φ₁ : A₁ ⟶ A₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A) (hιopen : ∀ i, IsOpenImmersion (ιD i))
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g) :
    ∃ (𝒱 : D₀.A.OrderedAffineCover) (lam₀ lam₀' : 𝒱.ι → 𝒰.ι) (hsub : ∀ v, 𝒱.U v ≤ 𝒰.U (lam₀' v))
      (n n' : ∀ v : 𝒱.ι, (↑(𝒱.U v) : Scheme.{0}) ⟶ ↑(𝒰.U (lam₀ v))),
      (∀ v, n v ≫ (𝒰.U (lam₀ v)).ι = D₀.A.homOfLE (hsub v) ≫ m (lam₀' v)) ∧
      (∀ v, n' v ≫ ιD (lam₀ v) = D₀.A.homOfLE (hsub v) ≫ mp (lam₀' v)) ∧
      (∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀ v)) ∧
      (∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤
        (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀' v)) := by
  classical

  have hSpecSurj : ∀ P : Spec (CommRingCat.of B), ∃ Q : Spec (CommRingCat.of B₁),
      (Spec.map (CommRingCat.ofHom (algebraMap B B₁))).base Q = P := by
    intro P
    obtain ⟨N, hN⟩ := hker
    have hle : (RingHom.ker (algebraMap B B₁) : Set B) ⊆ P.asIdeal := by
      intro x hx
      have hxN : x ^ N ∈ (RingHom.ker (algebraMap B B₁)) ^ N := Ideal.pow_mem_pow hx N
      rw [hN] at hxN
      have h0 : x ^ N = 0 := by simpa using hxN
      exact P.isPrime.mem_of_pow_mem N (by rw [h0]; exact zero_mem _)
    have hP : P ∈ Set.range (PrimeSpectrum.comap (algebraMap B B₁)) := by
      rw [range_comap_of_surjective _ (algebraMap B B₁) hπ]
      exact hle
    obtain ⟨Q, hQ⟩ := hP
    exact ⟨Q, hQ⟩
  have hgsurj : ∀ x : D₀.A, ∃ a : A₁, D₀.g.base a = x := by
    intro x
    obtain ⟨Q, hQ⟩ := hSpecSurj (D₀.f.base x)

    have hx : x ∈ Set.range (pullback.fst D₀.f (Spec.map (CommRingCat.ofHom (algebraMap B B₁)))).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨Q, hQ⟩
    obtain ⟨p, hp⟩ := hx
    refine ⟨(D₀.cart.isoPullback).inv.base p, ?_⟩
    have := D₀.cart.isoPullback_inv_fst
    show ((D₀.cart.isoPullback).inv ≫ D₀.g).base p = x
    rw [this]
    exact hp

  have hm_pt : ∀ (j : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j),
      (m j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩) = D₀.g.base (φ₁.base a) := by
    intro j a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U j))) (hmμ j)
    simpa [Scheme.Hom.comp_apply] using this
  have hmp_pt : ∀ (j : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j),
      (mp j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩) = D.g.base (φ₁.base a) := by
    intro j a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U j))) (hmpμ j)
    simpa [Scheme.Hom.comp_apply] using this
  have hιD_pt : ∀ (i : 𝒰.ι) (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U i),
      (ιD i).base ((D₀.g ∣_ 𝒰.U i).base ⟨a, ha⟩) = D.g.base a := by
    intro i a ha
    have := congrArg (fun φ => φ.base (⟨a, ha⟩ : ↥(D₀.g ⁻¹ᵁ 𝒰.U i))) (hιg i)
    simpa [Scheme.Hom.comp_apply] using this

  have hres : ∀ (j : 𝒰.ι) (y : ↥(𝒰.U j)), ∃ (a : A₁) (ha : D₀.g.base a ∈ 𝒰.U j), (D₀.g ∣_ 𝒰.U j).base ⟨a, ha⟩ = y := by
    intro j y
    obtain ⟨a, ha⟩ := hgsurj y.1
    refine ⟨a, by rw [ha]; exact y.2, ?_⟩
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact ha
  have hmem : ∀ x : D₀.A, ∃ j : 𝒰.ι, x ∈ 𝒰.U j := by
    intro x
    have : x ∈ (⊤ : D₀.A.Opens) := trivial
    rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at this
    exact this

  have hpt : ∀ x : D₀.A, ∃ (j i : 𝒰.ι) (V : D₀.A.Opens), IsAffineOpen V ∧ x ∈ V ∧ V ≤ 𝒰.U j ∧
      (∀ y : ↥(𝒰.U j), (y : D₀.A) ∈ V → (m j).base y ∈ 𝒰.U i) ∧
      (∀ y : ↥(𝒰.U j), (y : D₀.A) ∈ V → (mp j).base y ∈ Set.range (ιD i).base) := by
    intro x
    obtain ⟨a, rfl⟩ := hgsurj x
    obtain ⟨j, hj⟩ := hmem (D₀.g.base a)
    obtain ⟨i, hi⟩ := hmem (D₀.g.base (φ₁.base a))
    haveI := hιopen i

    let W' : (↑(𝒰.U j) : Scheme.{0}).Opens := (m j) ⁻¹ᵁ (𝒰.U i) ⊓ (mp j) ⁻¹ᵁ (ιD i).opensRange
    let W : D₀.A.Opens := (𝒰.U j).ι ''ᵁ W'
    have hy0 : (D₀.g ∣_ 𝒰.U j).base ⟨a, hj⟩ = ⟨D₀.g.base a, hj⟩ := Subtype.ext (morphismRestrict_base_coe _ _ _)
    have hxW' : (⟨D₀.g.base a, hj⟩ : ↥(𝒰.U j)) ∈ W' := by
      rw [← hy0]
      refine ⟨?_, ?_⟩
      · show (m j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, hj⟩) ∈ 𝒰.U i
        rw [hm_pt]; exact hi
      · show (mp j).base ((D₀.g ∣_ 𝒰.U j).base ⟨a, hj⟩) ∈ (ιD i).opensRange
        rw [hmp_pt]
        exact ⟨(D₀.g ∣_ 𝒰.U i).base ⟨φ₁.base a, hi⟩, hιD_pt i _ hi⟩
    have hxW : D₀.g.base a ∈ W := ⟨⟨D₀.g.base a, hj⟩, hxW', rfl⟩
    obtain ⟨V, hVaff, hxV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp D₀.A.isBasis_affineOpens) hxW
    have hWU : W ≤ 𝒰.U j := by
      refine (Scheme.Hom.image_le_opensRange _ W').trans ?_
      rw [Scheme.Opens.opensRange_ι]

    have hVW' : ∀ y : ↥(𝒰.U j), (y : D₀.A) ∈ V → y ∈ W' := by
      intro y hy
      obtain ⟨y', hy', hyy⟩ := hVW hy
      have : y' = y := Subtype.ext hyy
      rw [← this]; exact hy'
    refine ⟨j, i, V, hVaff, hxV, hVW.trans hWU, fun y hy => (hVW' y hy).1, fun y hy => (hVW' y hy).2⟩
  choose jj ii V hVaff hxV hVU hVm hVmp using hpt

  have hcompact : IsCompact (Set.univ : Set D₀.A) := by
    have hcov : (Set.univ : Set D₀.A) = ⋃ i : 𝒰.ι, (𝒰.U i : Set D₀.A) := by
      have := congrArg (fun U : D₀.A.Opens => (U : Set D₀.A)) 𝒰.iSup_eq_top
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] at this
      exact this.symm
    rw [hcov]
    exact isCompact_iUnion fun i => (𝒰.isAffineOpen i).isCompact
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun x => (V x : Set D₀.A)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let pt : Fin t.card → D₀.A := fun v => (t.equivFin.symm v).1
  let 𝒱 : D₀.A.OrderedAffineCover :=
    { ι := Fin t.card
      U := fun v => V (pt v)
      isAffineOpen := fun v => hVaff (pt v)
      iSup_eq_top := by
        apply top_le_iff.mp
        intro x _
        have hx := ht (Set.mem_univ x)
        simp only [Set.mem_iUnion] at hx
        obtain ⟨y, hyt, hxy⟩ := hx
        rw [TopologicalSpace.Opens.mem_iSup]
        refine ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
        show x ∈ V (t.equivFin.symm (t.equivFin ⟨y, hyt⟩)).1
        rw [Equiv.symm_apply_apply]
        exact hxy }
  haveI : ∀ i, IsOpenImmersion (ιD i) := hιopen

  have hrange_n : ∀ v : Fin t.card,
      Set.range (D₀.A.homOfLE (hVU (pt v)) ≫ m (jj (pt v))).base ⊆ Set.range (𝒰.U (ii (pt v))).ι.base := by
    rintro v _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (m (jj (pt v))).base ((D₀.A.homOfLE (hVU (pt v))).base z) ∈ 𝒰.U (ii (pt v))
    refine hVm (pt v) _ ?_
    rw [Scheme.homOfLE_apply]
    exact z.2
  have hrange_n' : ∀ v : Fin t.card,
      Set.range (D₀.A.homOfLE (hVU (pt v)) ≫ mp (jj (pt v))).base ⊆ Set.range (ιD (ii (pt v))).base := by
    rintro v _ ⟨z, rfl⟩
    show (mp (jj (pt v))).base ((D₀.A.homOfLE (hVU (pt v))).base z) ∈ Set.range (ιD (ii (pt v))).base
    refine hVmp (pt v) _ ?_
    rw [Scheme.homOfLE_apply]
    exact z.2
  refine ⟨𝒱, fun v => ii (pt v), fun v => jj (pt v), fun v => hVU (pt v),
    fun v => IsOpenImmersion.lift _ _ (hrange_n v), fun v => IsOpenImmersion.lift _ _ (hrange_n' v),
    fun v => IsOpenImmersion.lift_fac _ _ _, fun v => IsOpenImmersion.lift_fac _ _ _, ?_, ?_⟩
  ·
    intro v q hq
    change (pullback.fst D₀.f (specMap B (ResidueField B))).base q ∈ V (pt v) at hq
    show (pullback.fst D₀.f (specMap B (ResidueField B))).base (ψ.base q) ∈ 𝒰.U (ii (pt v))
    have h1 : (pullback.fst D₀.f (specMap B (ResidueField B))).base (ψ.base q) = D₀.g.base (φ₁.base (jκ.base q)) := by
      rw [← hjκ]
      show (ψ ≫ jκ ≫ D₀.g).base q = _
      rw [← Category.assoc, hψ₁]
      rfl
    have h2 : (pullback.fst D₀.f (specMap B (ResidueField B))).base q = D₀.g.base (jκ.base q) := by
      rw [← hjκ]; rfl
    rw [h1]
    rw [h2] at hq
    have ha : D₀.g.base (jκ.base q) ∈ 𝒰.U (jj (pt v)) := hVU (pt v) hq
    have := hVm (pt v) ((D₀.g ∣_ 𝒰.U (jj (pt v))).base ⟨jκ.base q, ha⟩) (by rw [morphismRestrict_base_coe]; exact hq)
    rwa [hm_pt] at this
  · intro v
    exact (pullback.fst D₀.f (specMap B (ResidueField B))).preimage_mono (hVU (pt v))

end S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_local_lifts_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_local_lifts_factor_bare (solution)
