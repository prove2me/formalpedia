-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_fourier_equiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:06:12.540617+00:00
-- url     : https://prove2.me/submissions/a3e9c304-c6df-403e-b061-714840045b78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Theorems.Thm_MasulloGRH_schwartzBruhat_stage_fourier
import Theorems.Thm_MasulloGRH_isStructuralPair_annihilator
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_LCAGroup_pontryagin_duality
import Theorems.Thm_LCAGroup_fourier_inversion
import Theorems.Thm_LCAGroup_plancherel
import Theorems.Thm_LCAGroup_fourier_L1_to_zeroAtInfty_injective

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_fourier_equiv

open MasulloGRH

universe u

/-! ### Continuity of Schwartz–Bruhat functions -/

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

theorem continuous_extendPullback {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hΓ : IsOpen (Γ : Set G)) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : Continuous π) (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) :
    Continuous (extendPullback Γ π g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hon : ContinuousOn (extendPullback Γ π g) (Γ : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Set.domRestrict (Γ : Set G) (extendPullback Γ π g) =
          fun y : (Γ : Set G) => g (Multiplicative.toAdd (π ⟨y.1, y.2⟩)) := by
        funext y
        show extendPullback Γ π g y.1 = _
        exact dif_pos y.2
      rw [this]
      exact hg.comp (continuous_toAdd.comp (hπ.comp (by fun_prop)))
    exact hon.continuousAt (hΓ.mem_nhds hx)
  · have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓ
    have h0 : extendPullback Γ π g =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp only [extendPullback, dif_neg (show y ∉ Γ from hy)]
    exact continuousAt_const.congr h0.symm

theorem continuous_sb {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : SchwartzBruhat G) : Continuous (f : G → ℂ) := by
  obtain ⟨f, hf⟩ := f
  show Continuous f
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact continuous_extendPullback Γ hs.1 π hπ.2.1 _ (continuous_elem g)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

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

theorem sb_top (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) = sInf (sbTops G) := rfl

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

/-! ### The Fourier transform on `S(G)` as a continuous linear map -/

section fourier

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

theorem integrable_mul_char {f : G → ℂ} (hf : Integrable f μ) (χ : PontryaginDual G) :
    Integrable (fun x => f x * star ((χ x : ℂ))) μ := by
  refine Integrable.mono' hf.norm (hf.aestronglyMeasurable.mul ?_) (ae_of_all _ fun x => ?_)
  · exact (continuous_star.comp (continuous_subtype_val.comp χ.continuous)).aestronglyMeasurable
  · rw [norm_mul, norm_star, Circle.norm_coe, mul_one]

theorem lcaFourier_add {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    RiemannMasullo.lcaFourier μ (f + g) =
      RiemannMasullo.lcaFourier μ f + RiemannMasullo.lcaFourier μ g := by
  funext χ
  simp only [RiemannMasullo.lcaFourier, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_char μ hf χ) (integrable_mul_char μ hg χ)

theorem lcaFourier_smul (c : ℂ) (f : G → ℂ) :
    RiemannMasullo.lcaFourier μ (c • f) = c • RiemannMasullo.lcaFourier μ f := by
  funext χ
  simp only [RiemannMasullo.lcaFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem lcaFourier_zero : RiemannMasullo.lcaFourier μ (0 : G → ℂ) = 0 := by
  funext χ
  simp [RiemannMasullo.lcaFourier]

theorem sb_mem (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    Integrable f μ ∧
      RiemannMasullo.lcaFourier μ f ∈ schwartzBruhatSubmodule (PontryaginDual G) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    obtain ⟨m', n', r', s', d', π', T, hπ', -, hT⟩ :=
      schwartzBruhat_stage_fourier G μ Γ k m n r s d π hs hπ
    refine ⟨(hT g).1, ?_⟩
    rw [(hT g).2]
    exact Submodule.subset_span ⟨_, _, m', n', r', s', d', π', T g,
      isStructuralPair_annihilator G Γ k hs, hπ', rfl⟩
  | zero => exact ⟨integrable_zero _ _ _, by rw [lcaFourier_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    exact ⟨hx.1.add hy.1, by rw [lcaFourier_add μ hx.1 hy.1]; exact Submodule.add_mem _ hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨hx.1.smul a, by rw [lcaFourier_smul]; exact Submodule.smul_mem _ a hx.2⟩

theorem integrable_sb (f : SchwartzBruhat G) : Integrable (f : G → ℂ) μ :=
  (sb_mem μ f.1 f.2).1

/-- The Fourier transform `S(G) → S(Ĝ)` as a linear map. -/
noncomputable def fourierLin : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat (PontryaginDual G) where
  toFun f := ⟨RiemannMasullo.lcaFourier μ f.1, (sb_mem μ f.1 f.2).2⟩
  map_add' f g := Subtype.ext (lcaFourier_add μ (sb_mem μ f.1 f.2).1 (sb_mem μ g.1 g.2).1)
  map_smul' c f := Subtype.ext (lcaFourier_smul μ c f.1)

theorem fourierLin_apply (f : SchwartzBruhat G) (χ : PontryaginDual G) :
    (fourierLin μ f : PontryaginDual G → ℂ) χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := rfl

theorem fourierLin_continuous : Continuous (fourierLin μ) := by
  apply continuous_of_stages
  intro Γ k m n r s d π hs hπ
  obtain ⟨m', n', r', s', d', π', T, hπ', hTc, hT⟩ :=
    schwartzBruhat_stage_fourier G μ Γ k m n r s d π hs hπ
  have : (fun g => fourierLin μ (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
      fun g => SchwartzBruhat.ofElem _ _ π' (isStructuralPair_annihilator G Γ k hs) hπ' (T g) := by
    funext g
    exact Subtype.ext (hT g).2
  rw [this]
  exact (continuous_ofElem _ _ _ _ _).comp hTc

/-- The Fourier transform `S(G) → S(Ĝ)` as a continuous linear map. -/
noncomputable def fourierCLM : SchwartzBruhat G →L[ℂ] SchwartzBruhat (PontryaginDual G) :=
  ⟨fourierLin μ, fourierLin_continuous μ⟩

theorem fourierCLM_apply (f : SchwartzBruhat G) (χ : PontryaginDual G) :
    (fourierCLM μ f : PontryaginDual G → ℂ) χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := rfl

end fourier

/-! ### Transport of Schwartz–Bruhat functions along isomorphisms of topological groups -/

section transport

variable {G H : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem cg_comap {X Y : Type*} [CommGroup X] [TopologicalSpace X] [CommGroup Y] [TopologicalSpace Y]
    (c : X ≃ₜ* Y) {A : Subgroup Y} (hA : IsCompactlyGeneratedSubgroup A) :
    IsCompactlyGeneratedSubgroup (A.comap (c.toMulEquiv : X →* Y)) := by
  obtain ⟨U, hU, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hA
  refine ⟨c ⁻¹' U, c.toHomeomorph.isCompact_preimage.2 hU, fun x hx => hUA hx,
    ⟨c ⁻¹' V, ?_, fun x hx => hVU ⟨hx.1, hx.2⟩⟩, ?_⟩
  · apply (map_continuous c).continuousAt.preimage_mem_nhds
    rw [map_one]
    exact hV
  · have himg : (c ⁻¹' U) = (c.toMulEquiv.symm : Y →* X) '' U := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        exact ⟨c x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [himg, ← MonoidHom.map_closure, hcl, Subgroup.comap_equiv_eq_map_symm]

/-- The dual isomorphism `Ĝ ≃ Ĥ`, `χ ↦ χ ∘ c⁻¹`. -/
noncomputable def dualEquiv (c : G ≃ₜ* H) : PontryaginDual G ≃ₜ* PontryaginDual H where
  toFun := PontryaginDual.map ⟨(c.symm.toMulEquiv : H →* G), c.symm.continuous⟩
  invFun := PontryaginDual.map ⟨(c.toMulEquiv : G →* H), c.continuous⟩
  left_inv χ := by
    ext x
    show ((χ (c.symm (c x)) : Circle) : ℂ) = χ x
    rw [ContinuousMulEquiv.symm_apply_apply]
  right_inv χ := by
    ext x
    show ((χ (c (c.symm x)) : Circle) : ℂ) = χ x
    rw [ContinuousMulEquiv.apply_symm_apply]
  map_mul' χ ψ := map_mul _ χ ψ
  continuous_toFun := (PontryaginDual.map _).continuous
  continuous_invFun := (PontryaginDual.map _).continuous

theorem dualEquiv_apply (c : G ≃ₜ* H) (χ : PontryaginDual G) (y : H) :
    dualEquiv c χ y = χ (c.symm y) := rfl

theorem annihilator_comap (c : G ≃ₜ* H) (k : Subgroup H) :
    MasulloGRH.annihilator (k.comap (c.toMulEquiv : G →* H)) =
      dualEquiv c ⁻¹' MasulloGRH.annihilator k := by
  ext χ
  simp only [MasulloGRH.annihilator, Set.mem_ofPred_eq, Set.mem_preimage, dualEquiv_apply,
    Subgroup.mem_comap]
  constructor
  · intro h y hy
    apply h
    show c (c.symm y) ∈ k
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact hy
  · intro h x hx
    have := h (c x) hx
    simpa using this

theorem good_comap (c : G ≃ₜ* H) {k : Subgroup H} (hk : IsGoodSubgroup k) :
    IsGoodSubgroup (k.comap (c.toMulEquiv : G →* H)) := by
  obtain ⟨hcl, hop, A, hA, hAcg⟩ := hk
  refine ⟨hcl.preimage (map_continuous c), ?_, A.comap ((dualEquiv c).toMulEquiv :
    PontryaginDual G →* PontryaginDual H), ?_, cg_comap (dualEquiv c) hAcg⟩
  · rw [annihilator_comap]
    exact hop.preimage (dualEquiv c).continuous
  · rw [annihilator_comap, ← hA]
    rfl

theorem structural_comap (c : G ≃ₜ* H) {Γ k : Subgroup H} (h : IsStructuralPair Γ k) :
    IsStructuralPair (Γ.comap (c.toMulEquiv : G →* H)) (k.comap (c.toMulEquiv : G →* H)) :=
  ⟨h.1.preimage (map_continuous c), cg_comap c h.2.1, good_comap c h.2.2.1, Subgroup.comap_mono h.2.2.2⟩

/-- The restriction of `c` to `c⁻¹(Γ) → Γ`. -/
noncomputable def restr (c : G ≃ₜ* H) (Γ : Subgroup H) :
    ↥(Γ.comap (c.toMulEquiv : G →* H)) →* ↥Γ :=
  (c.toMulEquiv : G →* H).subgroupComap Γ

theorem restr_apply (c : G ≃ₜ* H) (Γ : Subgroup H) (x : ↥(Γ.comap (c.toMulEquiv : G →* H))) :
    ((restr c Γ x : ↥Γ) : H) = c x := rfl

theorem pres_comap (c : G ≃ₜ* H) {Γ k : Subgroup H} {m n r s : ℕ} {d : Fin s → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m n r s d)} (hπ : IsElemPresentation Γ k π) :
    IsElemPresentation (Γ.comap (c.toMulEquiv : G →* H)) (k.comap (c.toMulEquiv : G →* H))
      (π.comp (restr c Γ)) := by
  obtain ⟨hd, hc, ho, hsurj, hker⟩ := hπ
  let e : ↥(Γ.comap (c.toMulEquiv : G →* H)) ≃ₜ ↥Γ :=
    c.toHomeomorph.subtype (fun x => Iff.rfl)
  have he : ⇑(restr c Γ) = ⇑e := rfl
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · show Continuous (π ∘ restr c Γ)
    rw [he]
    exact hc.comp e.continuous
  · show IsOpenMap (π ∘ restr c Γ)
    rw [he]
    exact ho.comp e.isOpenMap
  · show Function.Surjective (π ∘ restr c Γ)
    rw [he]
    exact hsurj.comp e.surjective
  · intro x
    rw [MonoidHom.comp_apply, hker (restr c Γ x), restr_apply, Subgroup.mem_comap]
    rfl

theorem extendPullback_comap (c : G ≃ₜ* H) (Γ : Subgroup H) {m n r s : ℕ} {d : Fin s → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g : ElemGroup m n r s d → ℂ) :
    extendPullback (Γ.comap (c.toMulEquiv : G →* H)) (π.comp (restr c Γ)) g =
      fun x => extendPullback Γ π g (c x) := by
  funext x
  by_cases hx : c x ∈ Γ
  · have hx' : x ∈ Γ.comap (c.toMulEquiv : G →* H) := hx
    simp only [extendPullback, dif_pos hx, dif_pos hx']
    rfl
  · have hx' : x ∉ Γ.comap (c.toMulEquiv : G →* H) := hx
    simp only [extendPullback, dif_neg hx, dif_neg hx']

theorem transport (c : G ≃ₜ* H) :
    ∃ R : SchwartzBruhat H →L[ℂ] SchwartzBruhat G, ∀ f x, R f x = f (c x) := by
  let L : (H → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ c
  have hL : ∀ f ∈ schwartzBruhatSubmodule H, L f ∈ schwartzBruhatSubmodule G := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨_, _, m, n, r, s, d, π.comp (restr c Γ), g, structural_comap c hs, pres_comap c hπ,
        (extendPullback_comap c Γ π g.toFun).symm⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  let R₀ : SchwartzBruhat H →ₗ[ℂ] SchwartzBruhat G := L.restrict hL
  have hcont : Continuous R₀ := by
    apply continuous_of_stages R₀
    intro Γ k m n r s d π hs hπ
    have : (fun g => R₀ (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
        fun g => SchwartzBruhat.ofElem _ _ (π.comp (restr c Γ)) (structural_comap c hs)
          (pres_comap c hπ) g := by
      funext g
      exact Subtype.ext (extendPullback_comap c Γ π g.toFun).symm
    rw [this]
    exact continuous_ofElem _ _ _ _ _
  exact ⟨⟨R₀, hcont⟩, fun f x => rfl⟩

end transport

end Sol_MasulloGRH_schwartzBruhat_fourier_equiv

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_fourier_equiv

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ : PontryaginDual G, F f χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := by
  letI : MeasurableSpace (PontryaginDual G) := borel _
  haveI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨ν, hν, -⟩ := (LCAGroup.plancherel G μ).1
  haveI : ν.IsHaarMeasure := hν.1
  haveI : ν.Regular := hν.2.1
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  let c : G ≃ₜ* PontryaginDual (PontryaginDual G) :=
    { toMulEquiv := (MulEquiv.inv G).trans e.toMulEquiv
      continuous_toFun := (map_continuous e).comp continuous_inv
      continuous_invFun := continuous_inv.comp (map_continuous e.symm) }
  have hc : ∀ (x : G) (χ : PontryaginDual G), c x χ = (χ x)⁻¹ := fun x χ => by
    show e x⁻¹ χ = _
    rw [he, map_inv]
  obtain ⟨R, hR⟩ := transport c
  let F := fourierCLM μ
  let F' := fourierCLM ν
  let S := R.comp F'
  have hS : ∀ (g : SchwartzBruhat (PontryaginDual G)) (x : G),
      (S g : G → ℂ) x = ∫ χ, (g : PontryaginDual G → ℂ) χ * (χ x : ℂ) ∂ν := by
    intro g x
    show (R (F' g) : G → ℂ) x = _
    rw [hR, fourierCLM_apply]
    unfold RiemannMasullo.lcaFourier
    congr 1
    funext χ
    rw [hc, Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj]
  have hSF : ∀ f, S (F f) = f := by
    intro f
    apply Subtype.ext
    funext x
    have h1 := hS (F f) x
    have hint : Integrable (RiemannMasullo.lcaFourier μ (f : G → ℂ)) ν := integrable_sb ν (F f)
    have h2 := (LCAGroup.fourier_inversion G μ ν hν (f : G → ℂ) (integrable_sb μ f) hint).2
      (continuous_sb f) x
    exact h1.trans h2.symm
  have hSinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ ξ, RiemannMasullo.lcaFourier ν (g : PontryaginDual G → ℂ) ξ = 0 := by
      intro ξ
      obtain ⟨x, rfl⟩ := c.surjective ξ
      have h1 : (R (F' g) : G → ℂ) x = 0 := by
        have := congrArg (fun h : SchwartzBruhat G => (h : G → ℂ) x) hg
        exact this
      rw [hR, fourierCLM_apply] at h1
      exact h1
    obtain ⟨Φ, hΦ, hinj, -⟩ := LCAGroup.fourier_L1_to_zeroAtInfty_injective (PontryaginDual G) ν
    have hgi : Integrable (g : PontryaginDual G → ℂ) ν := integrable_sb ν g
    have hL : hgi.toL1 _ = 0 := by
      apply hinj
      rw [map_zero]
      ext ξ
      rw [hΦ]
      have : RiemannMasullo.lcaFourier ν ((hgi.toL1 _ : Lp ℂ 1 ν) : PontryaginDual G → ℂ) ξ =
          RiemannMasullo.lcaFourier ν (g : PontryaginDual G → ℂ) ξ := by
        unfold RiemannMasullo.lcaFourier
        refine integral_congr_ae ?_
        filter_upwards [hgi.coeFn_toL1] with χ hχ
        rw [hχ]
      rw [this, h0]
      rfl
    have hae : (g : PontryaginDual G → ℂ) =ᵐ[ν] 0 := by
      have := hgi.coeFn_toL1
      rw [hL] at this
      exact this.symm.trans (Lp.coeFn_zero ℂ 1 ν)
    have hfun : (g : PontryaginDual G → ℂ) = 0 :=
      (Continuous.ae_eq_iff_eq ν (continuous_sb g) continuous_const).1 hae
    exact Subtype.ext hfun
  have hFS : ∀ g, F (S g) = g := fun g => hSinj (hSF (S g))
  exact ⟨ContinuousLinearEquiv.equivOfInverse F S hSF hFS,
    fun f => ⟨integrable_sb μ f, fun χ => rfl⟩⟩
