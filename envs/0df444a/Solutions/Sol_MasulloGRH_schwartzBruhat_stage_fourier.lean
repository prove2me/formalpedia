-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_stage_fourier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:56:20.373692+00:00
-- url     : https://prove2.me/submissions/9bf127a5-ba4f-46b4-be1a-fb4632a973f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_MasulloGRH_elemSchwartz_fourier_of_equiv_elemGroup
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup

open MeasureTheory Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Sol_MasulloGRH_schwartzBruhat_stage_fourier

open MasulloGRH Filter Function

/-- Compact sets lift along continuous open surjections out of locally compact spaces. -/
theorem exists_isCompact_image_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f) (ho : IsOpenMap f)
    (hs : Surjective f) {C : Set Y} (hC : IsCompact C) :
    ∃ C' : Set X, IsCompact C' ∧ f '' C' = C := by
  have hloc : ∀ y ∈ C, ∃ N : Set X, IsCompact N ∧ f '' N ∈ 𝓝 y := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x
    exact ⟨N, hNc, ho.image_mem_nhds hN⟩
  choose! N hNc hN using hloc
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover (fun y => f '' N y) hN
  have hL : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y hy => hNc y (htC y hy)
  refine ⟨(⋃ y ∈ t, N y) ∩ f ⁻¹' C, hL.inter_right (hC.isClosed.preimage hf), ?_⟩
  rw [Set.image_inter_preimage, Set.image_iUnion₂]
  exact Set.inter_eq_right.2 hcover

instance bs3 {n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)] :
    BorelSpace ((Fin n → UnitAddCircle) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) :=
  Prod.borelSpace

instance bsE {m n r s : ℕ} {d : Fin s → ℕ} [∀ i, NeZero (d i)] :
    BorelSpace (ElemGroup m n r s d) :=
  Prod.borelSpace

section dual

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Restriction of characters to a subgroup. -/
noncomputable def res (Γ : Subgroup G) : PontryaginDual G →ₜ* PontryaginDual Γ :=
  PontryaginDual.map ⟨Γ.subtype, continuous_subtype_val⟩

theorem res_apply (Γ : Subgroup G) (χ : PontryaginDual G) (x : Γ) : res Γ χ x = χ x := rfl

/-- For a closed subgroup, restriction of characters is open and onto (via the platform theorem
`LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup`). -/
theorem res_isOpenMap_surjective (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    IsOpenMap (res Γ) ∧ Surjective (res Γ) := by
  obtain ⟨e, he⟩ := LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup G Γ hΓ
  have h : (res Γ : PontryaginDual G → PontryaginDual Γ) =
      e ∘ (QuotientGroup.mk : PontryaginDual G → PontryaginDual G ⧸ LCAGroup.annihilator Γ) := by
    funext χ
    exact PontryaginDual.ext fun x => (he χ x).symm
  rw [h]
  exact ⟨e.toHomeomorph.isOpenMap.comp QuotientGroup.isOpenMap_coe,
    e.surjective.comp QuotientGroup.mk_surjective⟩

variable {m n r s : ℕ} {d : Fin s → ℕ}

instance instT2Mult (m n r s : ℕ) (d : Fin s → ℕ) : T2Space (Multiplicative (ElemGroup m n r s d)) :=
  inferInstanceAs (T2Space (ElemGroup m n r s d))

instance instLCMult (m n r s : ℕ) (d : Fin s → ℕ) :
    LocallyCompactSpace (Multiplicative (ElemGroup m n r s d)) :=
  inferInstanceAs (LocallyCompactSpace (ElemGroup m n r s d))

example (m n r s : ℕ) (d : Fin s → ℕ) : IsTopologicalGroup (Multiplicative (ElemGroup m n r s d)) :=
  inferInstance

theorem pi_ext {Γ : Subgroup G} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hsurj : Surjective π) {ψ₁ ψ₂ : PontryaginDual (Multiplicative (ElemGroup m n r s d))}
    (h : ∀ x, ψ₁ (π x) = ψ₂ (π x)) : ψ₁ = ψ₂ := by
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact congrArg (fun z : Circle => (z : ℂ)) (h x)

/-- The character of the elementary group induced by a character trivial on `k`. -/
noncomputable def rhoHom (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) :
    Multiplicative (ElemGroup m n r s d) →* Circle :=
  π.liftOfSurjective hπ.2.2.2.1
    ⟨(MonoidHomClass.toMonoidHom χ.1 : G →* Circle).comp Γ.subtype, fun x hx => by
      have h1 : (x : G) ∈ k := (hπ.2.2.2.2 x).1 (MonoidHom.mem_ker.1 hx)
      exact MonoidHom.mem_ker.2 (χ.2 x h1)⟩

theorem rhoHom_apply (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) (x : Γ) :
    rhoHom Γ k π hπ χ (π x) = χ.1 x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

noncomputable def rhoFun (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) :
    PontryaginDual (Multiplicative (ElemGroup m n r s d)) :=
  (⟨rhoHom Γ k π hπ χ, by
    have hq : IsQuotientMap π := (IsOpenQuotientMap.isQuotientMap ⟨hπ.2.2.2.1, hπ.2.1, hπ.2.2.1⟩)
    have hc : Continuous (⇑(rhoHom Γ k π hπ χ)) := hq.continuous_iff.2
      ((χ.1.continuous.comp continuous_subtype_val).congr fun x =>
        (rhoHom_apply Γ k π hπ χ x).symm)
    exact hc⟩ :
      Multiplicative (ElemGroup m n r s d) →ₜ* Circle)

theorem rhoFun_apply (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) (x : Γ) :
    rhoFun Γ k π hπ χ (π x) = χ.1 x :=
  rhoHom_apply Γ k π hπ χ x

/-- The map `k^⊥ → Ê` induced by restriction of characters to `Γ`. -/
noncomputable def rho (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) :
    LCAGroup.annihilator k →* PontryaginDual (Multiplicative (ElemGroup m n r s d)) where
  toFun := rhoFun Γ k π hπ
  map_one' := pi_ext hπ.2.2.2.1 fun x => by
    rw [rhoFun_apply]
    rfl
  map_mul' χ₁ χ₂ := pi_ext hπ.2.2.2.1 fun x => by
    show rhoFun Γ k π hπ (χ₁ * χ₂) (π x) =
      rhoFun Γ k π hπ χ₁ (π x) * rhoFun Γ k π hπ χ₂ (π x)
    rw [rhoFun_apply, rhoFun_apply, rhoFun_apply]
    rfl

theorem rho_apply (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) (x : Γ) :
    rho Γ k π hπ χ (π x) = χ.1 x :=
  rhoFun_apply Γ k π hπ χ x

theorem rho_continuous (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    Continuous (rho Γ k π hπ) := by
  have : LocallyCompactSpace Γ :=
    (Subgroup.isClosed_of_isOpen Γ hs.1).isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous_iff.2 ?_
  refine ContinuousMap.continuous_compactOpen.2 fun C hC U hU => ?_
  obtain ⟨C', hC', hCC'⟩ := exists_isCompact_image_eq hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 hC
  have hset : {χ : LCAGroup.annihilator k |
      Set.MapsTo ((ContinuousMonoidHom.toContinuousMap ∘ rho Γ k π hπ) χ) C U} =
      (fun χ : LCAGroup.annihilator k => ContinuousMonoidHom.toContinuousMap χ.1) ⁻¹'
        {f | Set.MapsTo f (Subtype.val '' C') U} := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← hCC', Set.mapsTo_image_iff, Set.mapsTo_image_iff]
    refine Iff.of_eq (congrArg (fun f => Set.MapsTo f C' U) (funext fun x => ?_))
    exact rho_apply Γ k π hπ χ x
  rw [hset]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo (hC'.image continuous_subtype_val) hU).preimage
    ((ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous.comp continuous_subtype_val)

theorem rho_lift (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (v : PontryaginDual G)
    (ψ : PontryaginDual (Multiplicative (ElemGroup m n r s d)))
    (hv : res Γ v = PontryaginDual.map ⟨π, hπ.2.1⟩ ψ) :
    ∃ h : v ∈ LCAGroup.annihilator k, rho Γ k π hπ ⟨v, h⟩ = ψ := by
  have hvx : ∀ x : Γ, v x = ψ (π x) := fun x =>
    congrArg (fun η : PontryaginDual Γ => η x) hv
  have hvk : v ∈ LCAGroup.annihilator k := fun x hx => by
    have h2 : π ⟨x, hs.2.2.2 hx⟩ = 1 := (hπ.2.2.2.2 _).2 hx
    have h3 := hvx ⟨x, hs.2.2.2 hx⟩
    rw [h2, map_one] at h3
    exact h3
  exact ⟨hvk, pi_ext hπ.2.2.2.1 fun x => by rw [rho_apply]; exact hvx x⟩

theorem rho_surjective (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    Surjective (rho Γ k π hπ) := by
  intro ψ
  obtain ⟨v, hv⟩ := (res_isOpenMap_surjective Γ (Subgroup.isClosed_of_isOpen Γ hs.1)).2
    (PontryaginDual.map ⟨π, hπ.2.1⟩ ψ)
  obtain ⟨h, h'⟩ := rho_lift Γ k π hs hπ v ψ hv
  exact ⟨⟨v, h⟩, h'⟩

theorem rho_isOpenMap (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    IsOpenMap (rho Γ k π hπ) := by
  obtain ⟨hro, -⟩ := res_isOpenMap_surjective Γ (Subgroup.isClosed_of_isOpen Γ hs.1)
  intro U hU
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  have key : rho Γ k π hπ '' (Subtype.val ⁻¹' V) =
      PontryaginDual.map ⟨π, hπ.2.1⟩ ⁻¹' (res Γ '' V) := by
    ext ψ
    constructor
    · rintro ⟨χ, hχV, rfl⟩
      refine ⟨χ.1, hχV, ?_⟩
      ext x
      exact congrArg (fun z : Circle => (z : ℂ)) (rho_apply Γ k π hπ χ x).symm
    · rintro ⟨v, hvV, hv⟩
      obtain ⟨h, h'⟩ := rho_lift Γ k π hs hπ v ψ hv
      exact ⟨⟨v, h⟩, hvV, h'⟩
  rw [key]
  exact (hro V hV).preimage (PontryaginDual.map ⟨π, hπ.2.1⟩).continuous

theorem rho_eq_one_iff (Γ k : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) (χ : LCAGroup.annihilator k) :
    rho Γ k π hπ χ = 1 ↔ (χ : PontryaginDual G) ∈ LCAGroup.annihilator Γ := by
  constructor
  · intro h x hx
    have := rho_apply Γ k π hπ χ ⟨x, hx⟩
    rw [h] at this
    exact this.symm
  · intro h
    refine pi_ext hπ.2.2.2.1 fun x => ?_
    rw [rho_apply]
    exact h x x.2

end dual

end Sol_MasulloGRH_schwartzBruhat_stage_fourier

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_stage_fourier Filter
open scoped Pointwise

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    ∃ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥(LCAGroup.annihilator k) →* Multiplicative (ElemGroup m' n' r' s' d'))
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'),
      IsElemPresentation (LCAGroup.annihilator k) (LCAGroup.annihilator Γ) π' ∧ Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        Integrable (extendPullback Γ π g.toFun) μ ∧
          RiemannMasullo.lcaFourier μ (extendPullback Γ π g.toFun) =
            extendPullback (LCAGroup.annihilator k) π' (T g).toFun := by
  classical
  have : ∀ i, NeZero (d i) := fun i => ⟨hπ.1 i⟩
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓo
  haveI : LocallyCompactSpace Γ := hΓc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hk : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  -- the Haar measure of `Γ`
  haveI hν : (μ.comap (Γ.subtype : Γ → G)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μ (f := Γ.subtype)
      hΓo.isOpenEmbedding_subtypeVal
  -- `π` is proper
  have hprop : Tendsto π (cocompact Γ) (cocompact (Multiplicative (ElemGroup m n r s d))) := by
    refine (hasBasis_cocompact.tendsto_iff hasBasis_cocompact).2 fun B hB => ?_
    obtain ⟨L, hL, hLB⟩ := exists_isCompact_image_eq hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 hB
    have hker : IsCompact (Subtype.val ⁻¹' (k : Set G) : Set Γ) :=
      hΓc.isClosedEmbedding_subtypeVal.isCompact_preimage hk
    refine ⟨L * (Subtype.val ⁻¹' (k : Set G)), hL.mul hker, fun x hx hxB => hx ?_⟩
    rw [← hLB] at hxB
    obtain ⟨x', hx'L, hx'⟩ := hxB
    refine ⟨x', hx'L, x'⁻¹ * x, ?_, mul_inv_cancel_left x' x⟩
    have h1 : π (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
    exact (hπ.2.2.2.2 _).1 h1
  -- the push-forward is a Haar measure on the elementary group
  letI : MeasurableSpace (Multiplicative (ElemGroup m n r s d)) :=
    (inferInstance : MeasurableSpace (ElemGroup m n r s d))
  haveI : BorelSpace (Multiplicative (ElemGroup m n r s d)) :=
    ⟨(BorelSpace.measurable_eq : (inferInstance : MeasurableSpace (ElemGroup m n r s d)) =
      borel (ElemGroup m n r s d))⟩
  haveI : ((μ.comap (Γ.subtype : Γ → G)).map π).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ π hπ.2.1 hπ.2.2.2.1 hprop
  obtain ⟨m', n', r', s', d', φ', T, hd', hT, hFT⟩ :=
    elemSchwartz_fourier_of_equiv_elemGroup (Multiplicative (ElemGroup m n r s d))
      ((μ.comap (Γ.subtype : Γ → G)).map π) m n r s d hπ.1 (ContinuousMulEquiv.refl _)
  let π' : LCAGroup.annihilator k →* Multiplicative (ElemGroup m' n' r' s' d') :=
    φ'.toMulEquiv.toMonoidHom.comp (rho Γ k π hπ)
  have hπ'apply : ∀ χ, π' χ = φ' (rho Γ k π hπ χ) := fun _ => rfl
  refine ⟨m', n', r', s', d', π', T, ⟨hd', ?_, ?_, ?_, ?_⟩, hT, fun g => ⟨?_, ?_⟩⟩
  · exact φ'.continuous.comp (rho_continuous Γ k π hs hπ)
  · exact φ'.toHomeomorph.isOpenMap.comp (rho_isOpenMap Γ k π hs hπ)
  · exact φ'.surjective.comp (rho_surjective Γ k π hs hπ)
  · intro χ
    rw [hπ'apply, ← rho_eq_one_iff Γ k π hπ χ]
    exact map_eq_one_iff φ' φ'.injective
  · -- integrability
    have hcomp : Integrable (fun x : Γ => g.toFun (Multiplicative.toAdd (π x)))
        (μ.comap (Γ.subtype : Γ → G)) :=
      (hFT g).1.comp_measurable hπ.2.1.measurable
    apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (Γ : Set G))
    · rw [integrableOn_iff_comap_subtypeVal hΓo.measurableSet]
      refine hcomp.congr (ae_of_all _ fun x => ?_)
      show g.toFun (Multiplicative.toAdd (π x)) = extendPullback Γ π g.toFun x.1
      simp only [extendPullback, dif_pos x.2]
    · intro x hx
      simp only [extendPullback, dif_neg (show x ∉ Γ from hx)]
  · funext χ
    by_cases hχ : χ ∈ LCAGroup.annihilator k
    · -- on `k^⊥`: the Fourier integral is computed on the elementary group
      have hR : extendPullback (LCAGroup.annihilator k) π' (T g).toFun χ =
          (T g).toFun (Multiplicative.toAdd (φ' (rho Γ k π hπ ⟨χ, hχ⟩))) := by
        simp only [extendPullback, dif_pos hχ]
        rfl
      rw [hR, ← congrFun (hFT g).2 (rho Γ k π hπ ⟨χ, hχ⟩)]
      unfold RiemannMasullo.lcaFourier
      have hmeas : AEStronglyMeasurable (fun y : Multiplicative (ElemGroup m n r s d) =>
          g.toFun (Multiplicative.toAdd ((ContinuousMulEquiv.refl _) y)) *
            star ((rho Γ k π hπ ⟨χ, hχ⟩ y : Circle) : ℂ)) ((μ.comap (Γ.subtype : Γ → G)).map π) :=
        (hFT g).1.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
      rw [integral_map hπ.2.1.aemeasurable hmeas]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Γ : Set G)) (fun x hx => by
        simp only [extendPullback, dif_neg (show x ∉ Γ from hx), zero_mul])]
      rw [← integral_subtype_comap hΓo.measurableSet]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show extendPullback Γ π g.toFun x.1 * star ((χ x.1 : Circle) : ℂ) =
        g.toFun (Multiplicative.toAdd (π x)) * star ((rho Γ k π hπ ⟨χ, hχ⟩ (π x) : Circle) : ℂ)
      rw [rho_apply]
      simp only [extendPullback]
      rw [dif_pos (show (x : G) ∈ Γ from x.2)]
      rfl
    · -- off `k^⊥`: translation by an element of `k` on which `χ` is not trivial
      have hR : extendPullback (LCAGroup.annihilator k) π' (T g).toFun χ = 0 := by
        simp only [extendPullback, dif_neg hχ]
      rw [hR]
      obtain ⟨u, hu, hχu⟩ : ∃ u ∈ k, χ u ≠ 1 := by
        by_contra h
        exact hχ fun u hu => by_contra fun h' => h ⟨u, hu, h'⟩
      have huΓ : u ∈ Γ := hs.2.2.2 hu
      have hinv : ∀ x, extendPullback Γ π g.toFun (u * x) = extendPullback Γ π g.toFun x := by
        intro x
        by_cases hx : x ∈ Γ
        · have hux : u * x ∈ Γ := Γ.mul_mem huΓ hx
          simp only [extendPullback, dif_pos hx, dif_pos hux]
          have h1 : (⟨u * x, hux⟩ : Γ) = ⟨u, huΓ⟩ * ⟨x, hx⟩ := rfl
          rw [h1, map_mul, (hπ.2.2.2.2 ⟨u, huΓ⟩).2 hu, one_mul]
        · have hux : u * x ∉ Γ := fun h => hx (by
            have := Γ.mul_mem (Γ.inv_mem huΓ) h
            rwa [inv_mul_cancel_left] at this)
          simp only [extendPullback, dif_neg hx, dif_neg hux]
      unfold RiemannMasullo.lcaFourier
      set c : ℂ := star ((χ u : Circle) : ℂ) with hcdef
      have hc : c ≠ 1 := by
        intro h
        apply hχu
        have h2 : ((χ u : Circle) : ℂ) = 1 := by
          have := congrArg star h
          rwa [hcdef, star_star, star_one] at this
        exact Circle.coe_eq_one.1 h2
      have heq : ∫ x, extendPullback Γ π g.toFun x * star ((χ x : Circle) : ℂ) ∂μ =
          c * ∫ x, extendPullback Γ π g.toFun x * star ((χ x : Circle) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        conv_lhs => rw [← integral_mul_left_eq_self
          (fun x => extendPullback Γ π g.toFun x * star ((χ x : Circle) : ℂ)) u]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hinv, map_mul, Circle.coe_mul, star_mul, hcdef]
        ring
      have h0 : (1 - c) * ∫ x, extendPullback Γ π g.toFun x * star ((χ x : Circle) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, ← heq, sub_self]
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h).symm hc
      · exact h
