-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_cosetIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:08:50.218065+00:00
-- url     : https://prove2.me/submissions/ea70367d-3678-4afd-a961-5d289b10e45d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_LCAGroup_Annihilator
import Theorems.Thm_MasulloGRH_elemSchwartz_fiberIntegral
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_isCompact_preimage_of_isOpenMap_of_isCompact_ker
import Theorems.Thm_LCAGroup_isCompact_iff_isOpen_annihilator
import Theorems.Thm_LCAGroup_dual_quotient_equiv_annihilator
import Theorems.Thm_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact
import Theorems.Thm_LCAGroup_pontryagin_duality
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_schwartzBruhat_averaging
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_cosetIntegral

open MasulloGRH

universe u

/-! ### The universal property of the inductive limit topology -/

/-- The set of topologies whose infimum is the topology of `S(G)`. -/
def sbTops (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Set (TopologicalSpace (SchwartzBruhat G)) :=
  {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)}

theorem continuous_ofElem {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ k : Subgroup G) {m n r s : ℕ} {d : Fin s → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  have h := (@continuous_sInf_rng _ _ (SchwartzBruhat.ofElem Γ k π hs hπ) _ (sbTops G)).2
    (fun t ht => ht.2 Γ k m n r s d π hs hπ)
  exact h

theorem continuous_of_stages {G H : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Φ : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat H)
    (hΦ : ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      Continuous (fun g => Φ (SchwartzBruhat.ofElem Γ k π hs hπ g))) :
    Continuous Φ := by
  have key : @Continuous _ _ (sInf (sbTops G)) (sInf (sbTops H)) Φ := by
    rw [continuous_sInf_rng]
    intro t' ht'
    rw [continuous_iff_le_induced]
    apply sInf_le
    refine ⟨?_, ?_⟩
    · obtain ⟨ι, hne, p, hp⟩ := ht'.1
      let _ : TopologicalSpace (SchwartzBruhat H) := t'
      exact ⟨ι, hne, p.comp Φ, LinearMap.withSeminorms_induced hp Φ⟩
    · intro Γ k m n r s d π hs hπ
      rw [continuous_induced_rng]
      have h1 : @Continuous _ _ _ (sInf (sbTops H)) _ := hΦ Γ k m n r s d π hs hπ
      exact continuous_le_rng (sInf_le ht') h1
  exact key

/-! ### One stage: the image pair and the reduction to the elementary fibre integral

For a structural pair `(Γ, k)` of `G` with presentation `π : Γ → E`, the image
`(q Γ, q k)` in `G ⧸ H` is structural; a presentation `π' : q Γ → E'` of it and `π` induce a
continuous open surjection `p : E → E'` with `p ∘ π = π' ∘ q`, whose kernel is `π (Γ ∩ H)`.
The restriction of `μ_H` to the open subgroup `Γ ∩ H` of `H`, pushed forward along the proper map
`Γ ∩ H → ker p`, is a Haar measure `ν` on `ker p`, and the coset integral of the stage function of
`g` becomes the fibre integral `∫_{ker p} g(y l) dν(l)`. -/

theorem cg_top_of_subgroup {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    (A : Subgroup X) (hA : IsCompactlyGeneratedSubgroup A) :
    ∃ U ∈ 𝓝 (1 : A), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨UA, hUAc, hUAA, ⟨VA, hVA, hVAU⟩, hgen⟩ := hA
  have himg : (Subtype.val : A → X) '' ((Subtype.val : A → X) ⁻¹' UA) = UA := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, hUAA hx⟩, hx, rfl⟩
  refine ⟨(Subtype.val : A → X) ⁻¹' UA, ?_, ?_, ?_⟩
  · exact Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hVA)
      (fun a ha => hVAU ⟨ha, a.2⟩)
  · rw [Subtype.isCompact_iff, himg]
    exact hUAc
  · apply Subgroup.map_injective A.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    show Subgroup.closure (Subtype.val '' (Subtype.val ⁻¹' UA)) = A
    rw [himg, hgen]

theorem cg_of_inducing {Y Z : Type*} [Group Y] [TopologicalSpace Y] [CommGroup Z]
    [TopologicalSpace Z] (ψ : Y →* Z) (hψc : Continuous ψ) (hψe : IsInducing ψ)
    (hY : ∃ U ∈ 𝓝 (1 : Y), IsCompact U ∧ Subgroup.closure U = ⊤) :
    IsCompactlyGeneratedSubgroup ψ.range := by
  obtain ⟨U, hU, hUc, hgen⟩ := hY
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Z), ψ ⁻¹' V ⊆ U := by
    rw [hψe.nhds_eq_comap, map_one] at hU
    exact Filter.mem_comap.1 hU
  refine ⟨ψ '' U, hUc.image hψc, ?_, ⟨V, hV, ?_⟩, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rintro _ ⟨hz, ⟨y, rfl⟩⟩
    exact ⟨y, hVU hz, rfl⟩
  · rw [← MonoidHom.map_closure, hgen, MonoidHom.range_eq_map]

theorem continuous_elem {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    Continuous g.toFun := by
  have hg := (isRapidDecay_elemSchwartz_toFun g).1
  let q : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)) id)
  have hq : IsQuotientMap q :=
    (IsOpenQuotientMap.id.prodMap
      ((IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).prodMap
        IsOpenQuotientMap.id)).isQuotientMap
  rw [hq.continuous_iff, continuous_iff_continuousAt]
  rintro ⟨x₀, t₀, a₀, b₀⟩
  have hcont : Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) => elemLift g.toFun a₀ b₀ (p.1, p.2.1)) :=
    (hg a₀ b₀).continuous.comp (by fun_prop)
  refine hcont.continuousAt.congr ?_
  have hopen : IsOpen {p : (Fin m → ℝ) × (Fin n → ℝ) × (Fin r → ℤ) ×
      ((i : Fin s) → ZMod (d i)) | p.2.2 = (a₀, b₀)} :=
    (isOpen_discrete {((a₀, b₀) : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))}).preimage
      (by fun_prop)
  filter_upwards [hopen.mem_nhds rfl] with p hp
  obtain ⟨x, t, a, b⟩ := p
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rfl

/-- The image of a structural pair in the quotient by a closed subgroup is structural. -/
theorem image_structural (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (Γ k : Subgroup G) (hs : IsStructuralPair Γ k) :
    IsStructuralPair (Γ.map (QuotientGroup.mk' H)) (k.map (QuotientGroup.mk' H)) := by
  have : IsClosed (H : Set G) := hH
  obtain ⟨hΓo, ⟨U, hUc, hUΓ, ⟨V, hV, hVU⟩, hUgen⟩, hkgood, hkΓ⟩ := hs
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hkgood
  obtain ⟨-, hko, Ak, hAk, hAkcg⟩ := hkgood
  have hqo : IsOpenMap (QuotientGroup.mk : G → G ⧸ H) := QuotientGroup.isOpenMap_coe
  refine ⟨?_, ?_, ?_, Subgroup.map_mono hkΓ⟩
  · rw [Subgroup.coe_map]
    exact hqo _ hΓo
  · refine ⟨QuotientGroup.mk' H '' U, hUc.image QuotientGroup.continuous_mk,
      Set.image_mono hUΓ, ⟨QuotientGroup.mk' H '' (V ∩ Γ), ?_, ?_⟩, ?_⟩
    · have h1 := hqo.image_mem_nhds (Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem))
      simpa using h1
    · rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨x, hVU hx, rfl⟩
    · rw [← MonoidHom.map_closure, hUgen]
  · -- the image of `k` is good
    have hkqc : IsCompact ((k.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) := by
      rw [Subgroup.coe_map]
      exact hkc.image QuotientGroup.continuous_mk
    have hkqcl : IsClosed ((k.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) :=
      hkqc.isClosed
    refine ⟨hkqcl, (LCAGroup.isCompact_iff_isOpen_annihilator (G ⧸ H) _ hkqcl).1 hkqc,
      LCAGroup.annihilator (k.map (QuotientGroup.mk' H)), rfl, ?_⟩
    obtain ⟨e, he⟩ := LCAGroup.dual_quotient_equiv_annihilator G H hH
    have hAko : IsOpen (Ak : Set (PontryaginDual G)) := by rw [hAk]; exact hko
    have : LocallyCompactSpace Ak := hAko.isOpenEmbedding_subtypeVal.locallyCompactSpace
    let M : Subgroup Ak := (LCAGroup.annihilator H).comap Ak.subtype
    have hMcl : IsClosed (M : Set Ak) := by
      have h1 : ((LCAGroup.annihilator H : Subgroup (PontryaginDual G)) : Set (PontryaginDual G))
          = ⋂ x ∈ H, (fun χ : PontryaginDual G => χ x) ⁻¹' {1} := by
        ext χ
        simp [LCAGroup.mem_annihilator_iff]
      have h2 : IsClosed ((LCAGroup.annihilator H : Subgroup (PontryaginDual G)) :
          Set (PontryaginDual G)) := by
        rw [h1]
        exact isClosed_biInter fun x _ =>
          isClosed_singleton.preimage
            (show Continuous fun χ : PontryaginDual G => χ x from
              continuous_eval_const (F := G →ₜ* Circle) x)
      exact h2.preimage continuous_subtype_val
    have hY := (LCAGroup.compactlyGenerated_closedSubgroup_and_quotient Ak
      (cg_top_of_subgroup Ak hAkcg) M hMcl).1
    let ι : M →* LCAGroup.annihilator H :=
      MonoidHom.codRestrict (Ak.subtype.comp M.subtype) _ (fun x => x.2)
    have hιc : Continuous ι :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hιi : IsInducing ι := by
      refine IsInducing.of_comp hιc continuous_subtype_val ?_
      have hcomp : IsInducing ((Subtype.val : Ak → PontryaginDual G) ∘ (Subtype.val : M → Ak)) :=
        IsInducing.subtypeVal.comp IsInducing.subtypeVal
      exact hcomp
    let ψ : M →* PontryaginDual (G ⧸ H) := (e.symm : LCAGroup.annihilator H →* _).comp ι
    have hψc : Continuous ψ := e.symm.continuous.comp hιc
    have hψi : IsInducing ψ := e.symm.toHomeomorph.isInducing.comp hιi
    have hrange : ψ.range = LCAGroup.annihilator (k.map (QuotientGroup.mk' H)) := by
      ext η
      constructor
      · rintro ⟨x, rfl⟩
        rw [LCAGroup.mem_annihilator_iff]
        rintro _ ⟨κ, hκ, rfl⟩
        have h1 := he (ψ x) κ
        have h2 : e (ψ x) = ι x := by
          show e (e.symm (ι x)) = ι x
          exact e.apply_symm_apply _
        rw [h2] at h1
        rw [show QuotientGroup.mk' H κ = (κ : G ⧸ H) from rfl, ← h1]
        have h3 : ((x : Ak) : PontryaginDual G) ∈ annihilator k := by
          rw [← hAk]; exact (x : Ak).2
        exact h3 κ hκ
      · intro hη
        have h3 : ((e η : LCAGroup.annihilator H) : PontryaginDual G) ∈ Ak := by
          show ((e η : LCAGroup.annihilator H) : PontryaginDual G) ∈ (Ak : Set (PontryaginDual G))
          rw [hAk]
          intro κ hκ
          rw [he]
          exact hη _ ⟨κ, hκ, rfl⟩
        refine ⟨⟨⟨_, h3⟩, (e η).2⟩, ?_⟩
        show e.symm (ι _) = η
        have h4 : ι ⟨⟨_, h3⟩, (e η).2⟩ = e η := rfl
        rw [h4, e.symm_apply_apply]
    rw [← hrange]
    exact cg_of_inducing ψ hψc hψi hY

theorem stage (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    IsStructuralPair (Γ.map (QuotientGroup.mk' H)) (k.map (QuotientGroup.mk' H)) ∧
    ∃ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥(Γ.map (QuotientGroup.mk' H)) →* Multiplicative (ElemGroup m' n' r' s' d'))
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'),
      IsElemPresentation (Γ.map (QuotientGroup.mk' H)) (k.map (QuotientGroup.mk' H)) π' ∧
      Continuous T ∧ Function.Surjective T ∧
      ∀ (g : ElemSchwartz m n r s d) (x : G),
        Integrable (fun h : H => extendPullback Γ π g.toFun (x * (h : G))) μH ∧
          extendPullback (Γ.map (QuotientGroup.mk' H)) π' (T g).toFun (x : G ⧸ H) =
            ∫ h : H, extendPullback Γ π g.toFun (x * (h : G)) ∂μH := by
  classical
  have : IsClosed (H : Set G) := hH
  have hs₁ := image_structural G H hH Γ k hs
  refine ⟨hs₁, ?_⟩
  obtain ⟨m', n', r', s', d', π', hπ'⟩ :=
    exists_elemPresentation_of_isStructuralPair (G ⧸ H) _ _ hs₁
  obtain ⟨hd, hπc, hπo, hπs, hπk⟩ := hπ
  obtain ⟨hd', hπ'c, hπ'o, hπ's, hπ'k⟩ := hπ'
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  have hkΓ : k ≤ Γ := hs.2.2.2
  let qΓ : Γ →* Γ.map (QuotientGroup.mk' H) := (QuotientGroup.mk' H).subgroupMap Γ
  have hqΓ : ∀ γ : Γ, (qΓ γ : G ⧸ H) = ((γ : G) : G ⧸ H) := fun γ => rfl
  have hqΓc : Continuous qΓ :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have hqΓo : IsOpenMap qΓ := by
    intro O hO
    have hO' : IsOpen ((QuotientGroup.mk : G → G ⧸ H) '' (Subtype.val '' O)) :=
      QuotientGroup.isOpenMap_coe _ (hΓo.isOpenMap_subtype_val _ hO)
    convert hO'.preimage continuous_subtype_val using 1
    ext y
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o.val, ⟨o, ho, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨o, ho, rfl⟩, hy⟩
      exact ⟨o, ho, Subtype.ext hy⟩
  let φ : Γ →* Multiplicative (ElemGroup m' n' r' s' d') := π'.comp qΓ
  have hφc : Continuous φ := hπ'c.comp hqΓc
  have hφo : IsOpenMap φ := hπ'o.comp hqΓo
  have hker : π.ker ≤ φ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ ⊢
    have hγk : (γ : G) ∈ k := (hπk γ).1 hγ
    exact (hπ'k (qΓ γ)).2 ⟨γ, hγk, rfl⟩
  let p : Multiplicative (ElemGroup m n r s d) →* Multiplicative (ElemGroup m' n' r' s' d') :=
    π.liftOfRightInverse (Function.surjInv hπs) (Function.rightInverse_surjInv hπs) ⟨φ, hker⟩
  have hp : ∀ γ : Γ, p (π γ) = π' (qΓ γ) := fun γ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ γ
  have hπq : IsQuotientMap π := hπo.isQuotientMap hπc hπs
  have hpc : Continuous p := by
    rw [hπq.continuous_iff]
    have h1 : (p ∘ π : Γ → Multiplicative (ElemGroup m' n' r' s' d')) = φ := funext hp
    rw [h1]
    exact hφc
  have hpo : IsOpenMap p := by
    intro O hO
    have h1 : p '' O = φ '' (π ⁻¹' O) := by
      ext y
      constructor
      · rintro ⟨e, he, rfl⟩
        obtain ⟨γ, rfl⟩ := hπs e
        exact ⟨γ, he, (hp γ).symm⟩
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨π γ, hγ, hp γ⟩
    rw [h1]
    exact hφo _ (hO.preimage hπc)
  have hps : Function.Surjective p := by
    intro y
    obtain ⟨z, rfl⟩ := hπ's y
    obtain ⟨γ, rfl⟩ := (QuotientGroup.mk' H).subgroupMap_surjective Γ z
    exact ⟨π γ, hp γ⟩
  -- the Haar measure on the kernel of `p`
  letI : MeasurableSpace (Multiplicative (ElemGroup m n r s d)) := borel _
  haveI : BorelSpace (Multiplicative (ElemGroup m n r s d)) := ⟨rfl⟩
  let H' : Subgroup H := Γ.comap H.subtype
  have hH'o : IsOpen (H' : Set H) := hΓo.preimage continuous_subtype_val
  have hH'c : IsClosed (H' : Set H) := Subgroup.isClosed_of_isOpen H' hH'o
  let μ' : Measure H' := Measure.comap Subtype.val μH
  have hμ' : μ'.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap μH (mH := inferInstance) (f := H'.subtype)
      hH'o.isOpenEmbedding_subtypeVal
  let ι : H' →* Γ := (H.subtype.comp H'.subtype).codRestrict Γ (fun h => h.2)
  have hιc : Continuous ι := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hρmem : ∀ h : H', π (ι h) ∈ p.ker := by
    intro h
    rw [MonoidHom.mem_ker, hp]
    have h1 : qΓ (ι h) = 1 := by
      apply Subtype.ext
      rw [hqΓ, OneMemClass.coe_one]
      exact (QuotientGroup.eq_one_iff _).2 h.1.2
    rw [h1, map_one]
  let ρ : H' →* p.ker := (π.comp ι).codRestrict p.ker hρmem
  have hρ : ∀ h : H', ((ρ h : p.ker) : Multiplicative (ElemGroup m n r s d)) = π (ι h) :=
    fun h => rfl
  have hρc : Continuous ρ := (hπc.comp hιc).subtype_mk _
  have hρs : Function.Surjective ρ := by
    rintro ⟨l, hl⟩
    obtain ⟨γ, rfl⟩ := hπs l
    rw [MonoidHom.mem_ker, hp] at hl
    obtain ⟨κ, hκ, hκγ⟩ := (hπ'k (qΓ γ)).1 hl
    have hκγ' : ((κ : G) : G ⧸ H) = ((γ : G) : G ⧸ H) := hκγ
    have hmem : (κ : G)⁻¹ * γ ∈ H := QuotientGroup.eq.mp hκγ'
    have hmemΓ : (κ : G)⁻¹ * γ ∈ Γ := Γ.mul_mem (Γ.inv_mem (hkΓ hκ)) γ.2
    refine ⟨⟨⟨(κ : G)⁻¹ * γ, hmem⟩, hmemΓ⟩, Subtype.ext ?_⟩
    rw [hρ]
    have hι : ι ⟨⟨(κ : G)⁻¹ * γ, hmem⟩, hmemΓ⟩ = (⟨κ, hkΓ hκ⟩ : Γ)⁻¹ * γ := Subtype.ext rfl
    rw [hι, map_mul, map_inv, (hπk ⟨κ, hkΓ hκ⟩).2 hκ, inv_one, one_mul]
  have : T2Space (Multiplicative (ElemGroup m n r s d)) :=
    (inferInstance : T2Space (ElemGroup m n r s d))
  have hρp : Filter.Tendsto ρ (Filter.cocompact H') (Filter.cocompact p.ker) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro S hS
    have : LocallyCompactSpace Γ := hΓo.isOpenEmbedding_subtypeVal.locallyCompactSpace
    have hkerc : IsCompact {x : Γ | π x = 1} := by
      have h1 : {x : Γ | π x = 1} = (Subtype.val : Γ → G) ⁻¹' k := by
        ext x
        exact hπk x
      rw [h1, Subtype.isCompact_iff]
      have h2 : (Subtype.val : Γ → G) '' ((Subtype.val : Γ → G) ⁻¹' k) = k := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ha
        · intro hx
          exact ⟨⟨x, hkΓ hx⟩, hx, rfl⟩
      rw [h2]
      exact hkc
    have hS' : IsCompact ((Subtype.val : p.ker → Multiplicative (ElemGroup m n r s d)) '' S) :=
      hS.image continuous_subtype_val
    have hT : IsCompact ((Subtype.val : Γ → G) '' (π ⁻¹' ((Subtype.val : p.ker → _) '' S))) :=
      (isCompact_preimage_of_isOpenMap_of_isCompact_ker π hπc hπo hkerc hS').image
        continuous_subtype_val
    have hj : IsClosedEmbedding (fun h : H' => ((h : H) : G)) :=
      hH.isClosedEmbedding_subtypeVal.comp hH'c.isClosedEmbedding_subtypeVal
    have hpre : IsCompact (ρ ⁻¹' S) := by
      refine (hj.isCompact_preimage hT).of_isClosed_subset (hS.isClosed.preimage hρc) ?_
      intro h hh
      exact ⟨ι h, ⟨ρ h, hh, rfl⟩, rfl⟩
    exact hpre.compl_mem_cocompact
  let ν : Measure p.ker := μ'.map ρ
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_map μ' ρ hρc hρs hρp
  obtain ⟨T, hTc, hTs, hT⟩ := elemSchwartz_fiberIntegral hd hd' p hpc hpo hps ν
  refine ⟨m', n', r', s', d', π', T, ⟨hd', hπ'c, hπ'o, hπ's, hπ'k⟩, hTc, hTs, ?_⟩
  intro g x
  set F : G → ℂ := extendPullback Γ π g.toFun with hF
  have hkey : ∀ γ₀ : Γ,
      Integrable (fun h : H => F ((γ₀ : G) * (h : G))) μH ∧
        ∫ h : H, F ((γ₀ : G) * (h : G)) ∂μH =
          (T g).toFun (Multiplicative.toAdd (π' (qΓ γ₀))) := by
    intro γ₀
    let Ψ : p.ker → ℂ := fun l =>
      g.toFun (Multiplicative.toAdd (π γ₀ * (l : Multiplicative (ElemGroup m n r s d))))
    have hΨc : Continuous Ψ := (continuous_elem g).comp
      (continuous_toAdd.comp (continuous_const.mul continuous_subtype_val))
    have hF0 : ∀ h : H, h ∉ (H' : Set H) → F ((γ₀ : G) * (h : G)) = 0 := by
      intro h hh
      simp only [hF, extendPullback]
      rw [dif_neg]
      intro hmem
      apply hh
      show (h : G) ∈ Γ
      have h1 : (h : G) = (γ₀ : G)⁻¹ * ((γ₀ : G) * h) := by group
      rw [h1]
      exact Γ.mul_mem (Γ.inv_mem γ₀.2) hmem
    have hFρ : ∀ h : H', F ((γ₀ : G) * ((h : H) : G)) = Ψ (ρ h) := by
      intro h
      have hmem : (γ₀ : G) * ((h : H) : G) ∈ Γ := Γ.mul_mem γ₀.2 h.2
      simp only [hF, extendPullback, dif_pos hmem]
      show g.toFun (Multiplicative.toAdd (π ⟨_, hmem⟩)) =
        g.toFun (Multiplicative.toAdd (π γ₀ * π (ι h)))
      rw [← map_mul]
      rfl
    have hmeas : MeasurableSet (H' : Set H) := hH'o.measurableSet
    have hsupp : Function.support (fun h : H => F ((γ₀ : G) * (h : G))) ⊆ (H' : Set H) :=
      fun h hh => by
        by_contra h'
        exact hh (hF0 h h')
    have hcomp : (fun h : H => F ((γ₀ : G) * (h : G))) ∘ (Subtype.val : H' → H) = Ψ ∘ ρ :=
      funext hFρ
    have hint := (hT g (π γ₀)).1
    have hval := (hT g (π γ₀)).2
    constructor
    · rw [← integrableOn_iff_integrable_of_support_subset hsupp,
        integrableOn_iff_comap_subtypeVal hmeas]
      have h1 : Integrable (Ψ ∘ ρ) μ' :=
        (integrable_map_measure hΨc.aestronglyMeasurable hρc.aemeasurable).1 hint
      rw [← hcomp] at h1
      exact h1
    · calc ∫ h : H, F ((γ₀ : G) * (h : G)) ∂μH
          = ∫ h in (H' : Set H), F ((γ₀ : G) * (h : G)) ∂μH :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
        _ = ∫ h : H', F ((γ₀ : G) * ((h : H) : G)) ∂μ' :=
            (integral_subtype_comap hmeas (fun h : H => F ((γ₀ : G) * (h : G)))).symm
        _ = ∫ h : H', Ψ (ρ h) ∂μ' := integral_congr_ae (Filter.Eventually.of_forall hFρ)
        _ = ∫ l, Ψ l ∂ν := (integral_map hρc.aemeasurable hΨc.aestronglyMeasurable).symm
        _ = (T g).toFun (Multiplicative.toAdd (p (π γ₀))) := hval.symm
        _ = (T g).toFun (Multiplicative.toAdd (π' (qΓ γ₀))) := by rw [hp]
  by_cases hx : (x : G ⧸ H) ∈ Γ.map (QuotientGroup.mk' H)
  · obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 hx
    have hγx' : ((γ : G) : G ⧸ H) = (x : G ⧸ H) := hγx
    have hmem : γ⁻¹ * x ∈ H := QuotientGroup.eq.mp hγx'
    set h₀ : H := ⟨γ⁻¹ * x, hmem⟩ with hh₀
    have hfun : (fun h : H => F (x * (h : G))) =
        fun h : H => F (((⟨γ, hγ⟩ : Γ) : G) * ((h₀ * h : H) : G)) := by
      funext h
      congr 1
      rw [Subgroup.coe_mul, hh₀]
      group
    obtain ⟨hI, hV⟩ := hkey ⟨γ, hγ⟩
    rw [hfun]
    refine ⟨hI.comp_mul_left h₀, ?_⟩
    rw [integral_mul_left_eq_self (fun h : H => F (((⟨γ, hγ⟩ : Γ) : G) * (h : G))) h₀, hV,
      ← hγx']
    have hq : ((γ : G) : G ⧸ H) ∈ Γ.map (QuotientGroup.mk' H) := ⟨γ, hγ, rfl⟩
    simp only [extendPullback, dif_pos hq]
    rfl
  · have hzero : ∀ h : H, F (x * (h : G)) = 0 := by
      intro h
      simp only [hF, extendPullback]
      rw [dif_neg]
      intro hmem
      apply hx
      refine ⟨x * h, hmem, ?_⟩
      show ((x * h : G) : G ⧸ H) = (x : G ⧸ H)
      rw [QuotientGroup.eq]
      have h1 : (x * (h : G))⁻¹ * x = (h : G)⁻¹ := by group
      rw [h1]
      exact H.inv_mem h.2
    simp_rw [hzero]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [integral_zero]
    simp only [extendPullback, dif_neg hx]


/-! ### Cofinality of the image pairs

Every structural pair `(Γ₁, k₁)` of `G ⧸ H` is dominated by the image of a structural pair of `G`.
The good subgroup is `k = B^⊥` for an open compactly generated subgroup `B ⊆ Ĝ` containing the
image of `k₁^⊥` under the dual of the quotient map (Pontryagin duality gives `k^⊥ = B`), and `Γ`
is generated by a compact lift of a generating set of `Γ₁`, by `k` and by a compact
neighbourhood of `1`. -/

/-- Cofinality of the images of structural pairs. -/
theorem cofinal (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (Γ₁ k₁ : Subgroup (G ⧸ H)) (hs : IsStructuralPair Γ₁ k₁) :
    ∃ Γ k : Subgroup G, IsStructuralPair Γ k ∧
      Γ₁ ≤ Γ.map (QuotientGroup.mk' H) ∧ k.map (QuotientGroup.mk' H) ≤ k₁ := by
  have : IsClosed (H : Set G) := hH
  obtain ⟨-, hΓ₁cg, ⟨hk₁c, -, A₁, hA₁, U₁, hU₁c, -, -, hU₁gen⟩, -⟩ := hs
  obtain ⟨UΓ, hUΓc, -, -, hUΓgen⟩ := hΓ₁cg
  let q : G →ₜ* G ⧸ H := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  let D : PontryaginDual (G ⧸ H) →ₜ* PontryaginDual G := PontryaginDual.map q
  -- the open compactly generated subgroup `B` of the dual group
  obtain ⟨W₀, hW₀c, hW₀n⟩ := exists_compact_mem_nhds (1 : PontryaginDual G)
  let B : Subgroup (PontryaginDual G) := Subgroup.closure (D '' U₁ ∪ W₀)
  have hBn : (B : Set (PontryaginDual G)) ∈ 𝓝 1 :=
    Filter.mem_of_superset hW₀n (fun χ hχ => Subgroup.subset_closure (Or.inr hχ))
  have hBo : IsOpen (B : Set (PontryaginDual G)) := Subgroup.isOpen_of_mem_nhds B hBn
  have hBcl : IsClosed (B : Set (PontryaginDual G)) := Subgroup.isClosed_of_isOpen B hBo
  -- its annihilator `k` in `G`
  let k : Subgroup G :=
    { carrier := {x | ∀ χ ∈ B, χ x = 1}
      mul_mem' := fun {a b} ha hb χ hχ => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha χ hχ, hb χ hχ, one_mul]
      one_mem' := fun χ _ => map_one χ
      inv_mem' := fun {a} ha χ hχ => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha χ hχ, inv_one] }
  have hkmem : ∀ x : G, x ∈ k ↔ ∀ χ ∈ B, χ x = 1 := fun x => Iff.rfl
  have hkcl : IsClosed (k : Set G) := by
    have hk : (k : Set G) = ⋂ χ ∈ B, (fun x => χ x) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, hkmem, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hk]
    exact isClosed_biInter fun χ _ => isClosed_singleton.preimage (map_continuous χ)
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  have hann : annihilator k = (B : Set (PontryaginDual G)) := by
    ext χ
    constructor
    · intro hχ
      by_contra hχB
      obtain ⟨ψ, hψB, hψχ⟩ :=
        pontryaginDual_separates_of_locallyCompact (PontryaginDual G) B hBcl χ hχB
      have hx : e.symm ψ ∈ k := by
        rw [hkmem]
        intro χ' hχ'
        have h1 := he (e.symm ψ) χ'
        rw [e.apply_symm_apply] at h1
        rw [← h1]
        exact hψB χ' hχ'
      apply hψχ
      have h2 := he (e.symm ψ) χ
      rw [e.apply_symm_apply] at h2
      rw [h2]
      exact hχ _ hx
    · intro hχ x hx
      exact hx χ hχ
  have hkgood : IsGoodSubgroup k := by
    refine ⟨hkcl, by rw [hann]; exact hBo, B, hann.symm, D '' U₁ ∪ W₀,
      (hU₁c.image D.continuous).union hW₀c, Subgroup.subset_closure,
      ⟨W₀, hW₀n, fun χ hχ => Or.inr hχ.1⟩, rfl⟩
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hkgood
  -- the image of `k` lies in `k₁`
  have hkk₁ : k.map (QuotientGroup.mk' H) ≤ k₁ := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxk
    obtain ⟨η, hηk, hηx⟩ := pontryaginDual_separates_of_locallyCompact (G ⧸ H) k₁ hk₁c _ hxk
    have hηA : η ∈ A₁ := by
      have h1 : η ∈ annihilator k₁ := hηk
      rw [← hA₁] at h1
      exact h1
    have hDη : D η ∈ B := by
      have h1 : D η ∈ A₁.map D.toMonoidHom := ⟨η, hηA, rfl⟩
      rw [← hU₁gen, MonoidHom.map_closure] at h1
      exact Subgroup.closure_mono (fun χ hχ => Or.inl hχ) h1
    exact hηx (hx _ hDη)
  -- the open compactly generated subgroup `Γ`
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : G)
  have hcover : UΓ ⊆ ⋃ x : G,
      (QuotientGroup.mk : G → G ⧸ H) '' (Homeomorph.mulLeft x '' interior V₀) := by
    intro z _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact Set.mem_iUnion.2 ⟨x, x, ⟨1, mem_interior_iff_mem_nhds.2 hV₀n, mul_one x⟩, rfl⟩
  obtain ⟨t, ht⟩ := hUΓc.elim_finite_subcover _
    (fun x => QuotientGroup.isOpenMap_coe _
      ((Homeomorph.mulLeft x).isOpenMap _ isOpen_interior)) hcover
  let U' : Set G := ⋃ x ∈ t, Homeomorph.mulLeft x '' V₀
  have hU'c : IsCompact U' :=
    t.isCompact_biUnion fun x _ => hV₀c.image (Homeomorph.mulLeft x).continuous
  let Γ : Subgroup G := Subgroup.closure (U' ∪ (k : Set G) ∪ V₀)
  have hΓn : (Γ : Set G) ∈ 𝓝 1 :=
    Filter.mem_of_superset hV₀n (fun y hy => Subgroup.subset_closure (Or.inr hy))
  have hΓo : IsOpen (Γ : Set G) := Subgroup.isOpen_of_mem_nhds Γ hΓn
  refine ⟨Γ, k, ⟨hΓo, ⟨U' ∪ (k : Set G) ∪ V₀, (hU'c.union hkc).union hV₀c,
    Subgroup.subset_closure, ⟨V₀, hV₀n, fun y hy => Or.inr hy.1⟩, rfl⟩, hkgood,
    fun y hy => Subgroup.subset_closure (Or.inl (Or.inr hy))⟩, ?_, hkk₁⟩
  rw [← hUΓgen, Subgroup.closure_le]
  intro z hz
  have hz' := ht hz
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨x, hxt, w, ⟨v, hv, rfl⟩, rfl⟩ := hz'
  refine ⟨x * v, Subgroup.subset_closure (Or.inl (Or.inl ?_)), rfl⟩
  exact Set.mem_biUnion hxt ⟨v, interior_subset hv, rfl⟩


/-! ### The coset integral -/

section coset

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The coset integral `Φ_H f (y) = ∫_H f(y₀ h) dμ_H(h)`, `y₀` a representative of `y`. -/
noncomputable def cosetInt (H : Subgroup G) (μH : Measure H) (f : G → ℂ) : G ⧸ H → ℂ :=
  fun y => ∫ h : H, f (y.out * (h : G)) ∂μH

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [BorelSpace G] in
/-- On a stage, the coset integral is the stage function of `T g` on the image pair. -/
theorem cosetInt_stage (H : Subgroup G) (μH : Measure H) (Γ : Subgroup G)
    {m n r s : ℕ} {d : Fin s → ℕ} (π : ↥Γ →* Multiplicative (ElemGroup m n r s d))
    {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (π' : ↥(Γ.map (QuotientGroup.mk' H)) →* Multiplicative (ElemGroup m' n' r' s' d'))
    (g : ElemSchwartz m n r s d) (g' : ElemSchwartz m' n' r' s' d')
    (hT : ∀ x : G, extendPullback (Γ.map (QuotientGroup.mk' H)) π' g'.toFun (x : G ⧸ H) =
      ∫ h : H, extendPullback Γ π g.toFun (x * (h : G)) ∂μH) :
    cosetInt H μH (extendPullback Γ π g.toFun) =
      extendPullback (Γ.map (QuotientGroup.mk' H)) π' g'.toFun := by
  funext y
  have h1 := hT y.out
  rw [QuotientGroup.out_eq'] at h1
  exact h1.symm

theorem key (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.Regular] (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    (∀ x : G, Integrable (fun h : H => f (x * (h : G))) μH) ∧
      cosetInt H μH f ∈ schwartzBruhatSubmodule (G ⧸ H) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    obtain ⟨hs₁, m', n', r', s', d', π', T, hπ', -, -, hT⟩ :=
      stage G H hH μH Γ k m n r s d π hs hπ
    refine ⟨fun x => (hT g x).1, ?_⟩
    rw [cosetInt_stage H μH Γ π π' g (T g) (fun x => (hT g x).2)]
    exact Submodule.subset_span ⟨_, _, m', n', r', s', d', π', T g, hs₁, hπ', rfl⟩
  | zero =>
    refine ⟨fun x => integrable_zero _ _ _, ?_⟩
    have h0 : cosetInt H μH (0 : G → ℂ) = 0 := by
      funext y
      simp [cosetInt]
    rw [h0]
    exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ =>
    refine ⟨fun x => (h₁.1 x).add (h₂.1 x), ?_⟩
    have h0 : cosetInt H μH (f₁ + f₂) = cosetInt H μH f₁ + cosetInt H μH f₂ := by
      funext y
      exact integral_add (h₁.1 _) (h₂.1 _)
    rw [h0]
    exact Submodule.add_mem _ h₁.2 h₂.2
  | smul c f₁ _ h₁ =>
    refine ⟨fun x => (h₁.1 x).smul c, ?_⟩
    have h0 : cosetInt H μH (c • f₁) = c • cosetInt H μH f₁ := by
      funext y
      exact integral_smul c _
    rw [h0]
    exact Submodule.smul_mem _ c h₁.2

/-- The coset integral as a linear map `S(G) → S(G/H)`. -/
noncomputable def phiLin (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.Regular] : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat (G ⧸ H) where
  toFun f := ⟨cosetInt H μH f.1, (key H hH μH f.1 f.2).2⟩
  map_add' f₁ f₂ := Subtype.ext (funext fun _ =>
    integral_add ((key H hH μH f₁.1 f₁.2).1 _) ((key H hH μH f₂.1 f₂.2).1 _))
  map_smul' c _ := Subtype.ext (funext fun _ => integral_smul c _)

theorem phiLin_val (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.Regular] (f : SchwartzBruhat G) :
    (phiLin H hH μH f).1 = cosetInt H μH f.1 := rfl

theorem phiLin_apply (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.Regular] (f : SchwartzBruhat G) (x : G) :
    phiLin H hH μH f (x : G ⧸ H) = ∫ h : H, f (x * (h : G)) ∂μH := by
  show ∫ h : H, f.1 ((x : G ⧸ H).out * (h : G)) ∂μH = ∫ h : H, f.1 (x * (h : G)) ∂μH
  have hmem : x⁻¹ * (x : G ⧸ H).out ∈ H :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : G ⧸ H)).symm
  set h₀ : H := ⟨x⁻¹ * (x : G ⧸ H).out, hmem⟩
  have hx : (x : G ⧸ H).out = x * (h₀ : G) := by
    simp [h₀]
  have hfun : (fun h : H => f.1 ((x : G ⧸ H).out * (h : G))) =
      fun h : H => f.1 (x * ((h₀ * h : H) : G)) := by
    funext h
    rw [hx, Subgroup.coe_mul, mul_assoc]
  rw [hfun]
  exact integral_mul_left_eq_self (fun h : H => f.1 (x * (h : G))) h₀

theorem phiLin_continuous (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.Regular] : Continuous (phiLin H hH μH) := by
  apply continuous_of_stages
  intro Γ k m n r s d π hs hπ
  obtain ⟨hs₁, m', n', r', s', d', π', T, hπ', hTc, -, hT⟩ :=
    stage G H hH μH Γ k m n r s d π hs hπ
  have heq : (fun g => phiLin H hH μH (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
      fun g => SchwartzBruhat.ofElem _ _ π' hs₁ hπ' (T g) := by
    funext g
    apply Subtype.ext
    rw [phiLin_val]
    exact cosetInt_stage H μH Γ π π' g (T g) (fun x => (hT g x).2)
  rw [heq]
  exact (continuous_ofElem _ _ π' hs₁ hπ').comp hTc

theorem phiLin_surjective (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.Regular] : Function.Surjective (phiLin H hH μH) := by
  obtain ⟨A, hA1, hA2, -, -⟩ := schwartzBruhat_averaging (G ⧸ H)
  rintro ⟨F, hF⟩
  suffices hsuff : ∃ f : SchwartzBruhat G, (phiLin H hH μH f).1 = F by
    obtain ⟨f, hf⟩ := hsuff
    exact ⟨f, Subtype.ext hf⟩
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ₁, k₁, m₁, n₁, r₁, s₁, d₁, π₁, g₁, hs, hπ, rfl⟩ := hx
    obtain ⟨Γ, k, hsG, hΓ, hk⟩ := cofinal G H hH Γ₁ k₁ hs
    obtain ⟨m, n, r, s, d, π, hπG⟩ := exists_elemPresentation_of_isStructuralPair G Γ k hsG
    obtain ⟨hs₂, m', n', r', s', d', π', T, hπ', -, hTs, hT⟩ :=
      stage G H hH μH Γ k m n r s d π hsG hπG
    have h2 := hA2 Γ₁ k₁ m₁ n₁ r₁ s₁ d₁ π₁ hs hπ _ _ hs₂ hΓ hk g₁
    obtain ⟨g', hg'⟩ := hA1 _ _ m' n' r' s' d' π' hs₂ hπ' (SchwartzBruhat.ofElem Γ₁ k₁ π₁ hs hπ g₁)
    obtain ⟨g, rfl⟩ := hTs g'
    refine ⟨SchwartzBruhat.ofElem Γ k π hsG hπG g, ?_⟩
    rw [phiLin_val]
    show cosetInt H μH (extendPullback Γ π g.toFun) = _
    rw [cosetInt_stage H μH Γ π π' g (T g) (fun x => (hT g x).2)]
    have h3 := congrArg Subtype.val (h2.symm.trans hg')
    exact h3.symm
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add F₁ F₂ _ _ h₁ h₂ =>
    obtain ⟨f₁, hf₁⟩ := h₁
    obtain ⟨f₂, hf₂⟩ := h₂
    refine ⟨f₁ + f₂, ?_⟩
    rw [map_add]
    show (phiLin H hH μH f₁).1 + (phiLin H hH μH f₂).1 = _
    rw [hf₁, hf₂]
  | smul c F₁ _ h₁ =>
    obtain ⟨f₁, hf₁⟩ := h₁
    refine ⟨c • f₁, ?_⟩
    rw [map_smul]
    show c • (phiLin H hH μH f₁).1 = _
    rw [hf₁]

end coset

end Sol_MasulloGRH_schwartzBruhat_cosetIntegral

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_cosetIntegral

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] :
    ∃ Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H),
      Function.Surjective Φ ∧
      ∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun h : H => f (x * (h : G))) μH ∧
        Φ f (x : G ⧸ H) = ∫ h : H, f (x * (h : G)) ∂μH := by
  refine ⟨⟨phiLin H hH μH, phiLin_continuous H hH μH⟩, phiLin_surjective H hH μH, ?_⟩
  intro f x
  exact ⟨(key H hH μH f.1 f.2).1 x, phiLin_apply H hH μH f x⟩
