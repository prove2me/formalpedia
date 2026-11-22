-- Prove2me | solution 1 for MasulloGRH.sLocalFourier_schwartzBruhat_equiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:34:54.914862+00:00
-- url     : https://prove2.me/submissions/10cf58a7-6a76-451f-afcf-abacb4b30f77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_MasulloGRH_schwartzBruhat_fourier_equiv
import Theorems.Thm_MasulloGRH_sStdCharacter_pontryaginDual_equiv
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_selfDual_sStdCharacter
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

/-!
# The `S`-adelic Fourier transform is a topological automorphism of `S(𝔸_{F,S})`

Reduction to
* `MasulloGRH.schwartzBruhat_fourier_equiv`: for a Hausdorff LCA group `G` with a regular Haar
  measure `μ`, Schwartz–Bruhat functions are `μ`-integrable and the Fourier transform
  `f ↦ (χ ↦ ∫ f · χ̄ dμ)` is a continuous linear isomorphism `S(G) ≃ S(Ĝ)`;
* `MasulloGRH.sStdCharacter_pontryaginDual_equiv`: `y ↦ ψ_{S,std}(· y)` is an isomorphism of
  topological groups `𝔸_{F,S} ≃ \widehat{𝔸_{F,S}}`;
* the Proved theorems `MasulloGRH.sAdditiveTamagawa_selfDual_sStdCharacter` (`ψ_{S,std}` is a
  continuous unitary character and Fourier inversion holds for `ν_S`),
  `MasulloGRH.sAdditiveTamagawa_isAddHaarMeasure` and
  `RiemannMasullo.locallyCompactSpace_adicCompletion`.

Proved here: pulling back Schwartz–Bruhat functions along an isomorphism of topological groups is a
continuous linear isomorphism of Schwartz–Bruhat spaces (`pullCLE`); `ν_S` is regular; Fourier
transforms of integrable functions are continuous.
-/

set_option linter.style.haveILetI false

namespace Sol_MasulloGRH_sLocalFourier_schwartzBruhat_equiv

open MasulloGRH

universe u

noncomputable section

set_option linter.unusedSectionVars false

section transport

variable {G H : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The isomorphism of Pontryagin duals induced by a topological group isomorphism. -/
def dualEquiv (e : G ≃ₜ* H) : PontryaginDual G ≃ₜ* PontryaginDual H where
  toFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  invFun := PontryaginDual.map (ContinuousMonoidHom.toContinuousMonoidHom e)
  left_inv χ := by ext x; simp
  right_inv χ := by ext x; simp
  map_mul' := map_mul _
  continuous_toFun := (PontryaginDual.map _).continuous
  continuous_invFun := (PontryaginDual.map _).continuous

theorem dualEquiv_apply (e : G ≃ₜ* H) (χ : PontryaginDual G) (y : H) :
    dualEquiv e χ y = χ (e.symm y) := rfl

/-- `e` as a monoid homomorphism. -/
abbrev eh (e : G ≃ₜ* H) : G →* H := e.toMulEquiv.toMonoidHom

theorem cg_comap (e : G ≃ₜ* H) {A : Subgroup H} (hA : IsCompactlyGeneratedSubgroup A) :
    IsCompactlyGeneratedSubgroup (A.comap (eh e)) := by
  obtain ⟨U, hU, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hA
  refine ⟨e ⁻¹' U, e.toHomeomorph.isCompact_preimage.mpr hU, fun x hx => hUA hx,
    ⟨e ⁻¹' V, ?_, fun x hx => hVU ⟨hx.1, hx.2⟩⟩, ?_⟩
  · apply (map_continuous e).continuousAt.preimage_mem_nhds
    simpa using hV
  · rw [← hcl, Subgroup.comap_equiv_eq_map_symm' e.toMulEquiv, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy

theorem annihilator_comap (e : G ≃ₜ* H) (k : Subgroup H) :
    annihilator (k.comap (eh e)) = dualEquiv e ⁻¹' annihilator k := by
  ext χ
  simp only [annihilator, Set.mem_setOf_eq, Set.mem_preimage, dualEquiv_apply]
  constructor
  · intro h y hy
    apply h
    show e (e.symm y) ∈ k
    simpa using hy
  · intro h x hx
    have := h (e x) hx
    simpa using this

theorem good_comap (e : G ≃ₜ* H) {k : Subgroup H} (hk : IsGoodSubgroup k) :
    IsGoodSubgroup (k.comap (eh e)) := by
  obtain ⟨hcl, hop, A, hA, hAcg⟩ := hk
  refine ⟨hcl.preimage e.continuous, ?_, A.comap (eh (dualEquiv e)), ?_, cg_comap _ hAcg⟩
  · rw [annihilator_comap]
    exact hop.preimage (dualEquiv e).continuous
  · rw [annihilator_comap]
    show (dualEquiv e) ⁻¹' (A : Set _) = _
    rw [hA]

theorem structural_comap (e : G ≃ₜ* H) {Γ k : Subgroup H} (hs : IsStructuralPair Γ k) :
    IsStructuralPair (Γ.comap (eh e)) (k.comap (eh e)) :=
  ⟨hs.1.preimage e.continuous, cg_comap e hs.2.1, good_comap e hs.2.2.1,
    Subgroup.comap_mono hs.2.2.2⟩

/-- The restriction `Γ' = e⁻¹ Γ → Γ` of `e`. -/
abbrev restr (e : G ≃ₜ* H) (Γ : Subgroup H) : Γ.comap (eh e) →* Γ := (eh e).subgroupComap Γ

theorem restr_apply (e : G ≃ₜ* H) (Γ : Subgroup H) (x : Γ.comap (eh e)) :
    ((restr e Γ x : Γ) : H) = e x := rfl

theorem restr_isOpenMap (e : G ≃ₜ* H) (Γ : Subgroup H) : IsOpenMap (restr e Γ) := by
  have h : (restr e Γ : Γ.comap (eh e) → Γ) =
      (e.toHomeomorph.subtype (p := fun x => x ∈ Γ.comap (eh e)) (q := fun y => y ∈ Γ)
        (fun x => Iff.rfl)) := by
    funext x; rfl
  rw [h]
  exact Homeomorph.isOpenMap _

theorem restr_continuous (e : G ≃ₜ* H) (Γ : Subgroup H) : Continuous (restr e Γ) :=
  Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _

theorem restr_surjective (e : G ≃ₜ* H) (Γ : Subgroup H) : Function.Surjective (restr e Γ) := by
  intro y
  refine ⟨⟨e.symm y, ?_⟩, ?_⟩
  · show e (e.symm y) ∈ Γ
    simp
  · apply Subtype.ext
    exact e.apply_symm_apply _

theorem presentation_comap (e : G ≃ₜ* H) {m n r s : ℕ} {d : Fin s → ℕ} {Γ k : Subgroup H}
    {π : Γ →* Multiplicative (ElemGroup m n r s d)} (hπ : IsElemPresentation Γ k π) :
    IsElemPresentation (Γ.comap (eh e)) (k.comap (eh e)) (π.comp (restr e Γ)) := by
  obtain ⟨hd, hc, ho, hsu, hker⟩ := hπ
  refine ⟨hd, hc.comp (restr_continuous e Γ), ho.comp (restr_isOpenMap e Γ),
    hsu.comp (restr_surjective e Γ), fun x => ?_⟩
  exact hker (restr e Γ x)

theorem extendPullback_comp (e : G ≃ₜ* H) {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π g ∘ e = extendPullback (Γ.comap (eh e)) (π.comp (restr e Γ)) g := by
  funext x
  simp only [Function.comp_apply, extendPullback]
  by_cases h : e x ∈ Γ
  · rw [dif_pos h, dif_pos (show x ∈ Γ.comap (eh e) from h)]
    rfl
  · rw [dif_neg h, dif_neg (show x ∉ Γ.comap (eh e) from h)]

theorem mem_comp (e : G ≃ₜ* H) {f : H → ℂ} (hf : f ∈ schwartzBruhatSubmodule H) :
    f ∘ e ∈ schwartzBruhatSubmodule G := by
  have hle : schwartzBruhatSubmodule H ≤
      (schwartzBruhatSubmodule G).comap (LinearMap.funLeft ℂ ℂ e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    show extendPullback Γ π g.toFun ∘ e ∈ schwartzBruhatSubmodule G
    rw [extendPullback_comp]
    exact Submodule.subset_span ⟨_, _, m, n, r, s, d, _, g, structural_comap e hs,
      presentation_comap e hπ, rfl⟩
  exact hle hf

/-- Pull-back of Schwartz–Bruhat functions along `e`, as a linear map. -/
def pullLin (e : G ≃ₜ* H) : SchwartzBruhat H →ₗ[ℂ] SchwartzBruhat G where
  toFun f := ⟨f.1 ∘ e, mem_comp e f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullLin_apply (e : G ≃ₜ* H) (f : SchwartzBruhat H) (x : G) :
    (pullLin e f).toFun x = f.toFun (e x) := rfl

theorem pullLin_ofElem (e : G ≃ₜ* H) {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    (pullLin e ∘ SchwartzBruhat.ofElem Γ k π hs hπ) =
      SchwartzBruhat.ofElem (Γ.comap (eh e)) (k.comap (eh e)) (π.comp (restr e Γ))
        (structural_comap e hs) (presentation_comap e hπ) := by
  funext g
  apply Subtype.ext
  exact extendPullback_comp e Γ π g.toFun

theorem pullLin_continuous (e : G ≃ₜ* H) : Continuous (pullLin e) := by
  rw [continuous_iff_le_induced]
  show sInf _ ≤ TopologicalSpace.induced _ (sInf _)
  rw [induced_sInf]
  apply le_sInf
  rintro _ ⟨t, ⟨hlc, hst⟩, rfl⟩
  apply sInf_le
  refine ⟨?_, ?_⟩
  · obtain ⟨ι, hne, p, hp⟩ := hlc
    letI : TopologicalSpace (SchwartzBruhat G) := t
    exact ⟨ι, hne, p.comp (pullLin e), LinearMap.withSeminorms_induced hp (pullLin e)⟩
  · intro Γ k m n r s d π hs hπ
    rw [continuous_induced_rng]
    show @Continuous _ _ _ t (pullLin e ∘ SchwartzBruhat.ofElem Γ k π hs hπ)
    rw [pullLin_ofElem]
    exact hst _ _ m n r s d _ _ _

/-- Pull-back along a topological group isomorphism, as a continuous linear equivalence. -/
def pullCLE (e : G ≃ₜ* H) : SchwartzBruhat H ≃L[ℂ] SchwartzBruhat G :=
  ContinuousLinearEquiv.equivOfInverse ⟨pullLin e, pullLin_continuous e⟩
    ⟨pullLin e.symm, pullLin_continuous e.symm⟩
    (fun f => Subtype.ext (funext fun x => by
      show f.toFun (e (e.symm x)) = f.toFun x
      rw [e.apply_symm_apply]))
    (fun f => Subtype.ext (funext fun x => by
      show f.toFun (e.symm (e x)) = f.toFun x
      rw [e.symm_apply_apply]))

theorem pullCLE_apply (e : G ≃ₜ* H) (f : SchwartzBruhat H) (x : G) :
    (pullCLE e f).toFun x = f.toFun (e x) := rfl

end transport

/-- Inversion `x ↦ x⁻¹` of a topological abelian group, as an isomorphism of topological
groups. -/
def invCME (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] : G ≃ₜ* G :=
  { MulEquiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }

section adeles

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

theorem secondCountable_finite (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

end adeles

end

end Sol_MasulloGRH_sLocalFourier_schwartzBruhat_equiv

open MasulloGRH Sol_MasulloGRH_sLocalFourier_schwartzBruhat_equiv in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ f : SAdelicSchwartz F Sf, Integrable f.eval (sAdditiveTamagawa F Sf)) ∧
    ∃ T : SAdelicSchwartz F Sf ≃L[ℂ] SAdelicSchwartz F Sf,
      (∀ f : SAdelicSchwartz F Sf, (T f).eval = sLocalFourier Sf f.eval) ∧
      ∀ (f : SAdelicSchwartz F Sf) (x : SAdeleRing F Sf), (T (T f)).eval x = f.eval (-x) := by
  -- topology and measurable structure of `𝔸_{F,S}`
  haveI hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  haveI hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  haveI hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  haveI : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  haveI : LocallyCompactSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (LocallyCompactSpace ((w : InfinitePlace F) → w.Completion))
  haveI hA_bor : BorelSpace (SAdeleRing F Sf) := inferInstance
  haveI hA_lc : LocallyCompactSpace (SAdeleRing F Sf) := inferInstance
  haveI hA_sc : SecondCountableTopology (SAdeleRing F Sf) := inferInstance
  -- the measure `ν_S`
  set ν := sAdditiveTamagawa F Sf with hνdef
  haveI hν : ν.IsAddHaarMeasure := sAdditiveTamagawa_isAddHaarMeasure F Sf
  have hνreg : ν.Regular := by
    obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : SAdeleRing F Sf)
    exact Measure.regular_of_isAddLeftInvariant hK ⟨0, mem_interior_iff_mem_nhds.mpr hK0⟩
      hK.measure_lt_top.ne
  -- the same data on the multiplicative notation `G = 𝔸_{F,S}` used for Schwartz–Bruhat spaces
  let G := Multiplicative (SAdeleRing F Sf)
  letI mG : MeasurableSpace G := (inferInstance : MeasurableSpace (SAdeleRing F Sf))
  haveI : BorelSpace G := inferInstanceAs (BorelSpace (SAdeleRing F Sf))
  haveI : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) ×
      ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))
  haveI : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (SAdeleRing F Sf))
  let μ : Measure G := ν
  haveI hμ : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x => hν.map_add_left_eq_self (Multiplicative.toAdd x) }
  haveI hμreg : μ.Regular := hνreg
  -- the Fourier transform `S(G) ≃ S(Ĝ)` and the self-duality `G ≃ Ĝ`
  obtain ⟨FG, hFG⟩ := schwartzBruhat_fourier_equiv G μ
  obtain ⟨e, he⟩ := sStdCharacter_pontryaginDual_equiv F Sf
  obtain ⟨_, _, hψc, hinv⟩ := sAdditiveTamagawa_selfDual_sStdCharacter F Sf
  have hψn : ∀ x : SAdeleRing F Sf, ‖sStdCharacter Sf x‖ = 1 :=
    (sAdditiveTamagawa_selfDual_sStdCharacter F Sf).2.1
  let e' : G ≃ₜ* PontryaginDual G := (invCME G).trans e
  have he' : ∀ x y : SAdeleRing F Sf,
      star ((e' (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
        sStdCharacter Sf (x * y) := by
    intro x y
    have h1 : e' (Multiplicative.ofAdd y) = (e (Multiplicative.ofAdd y))⁻¹ := by
      show e (Multiplicative.ofAdd y)⁻¹ = _
      exact map_inv e _
    rw [h1, ← he x y]
    show star (((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x))⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj]
    exact star_star _
  -- the `S`-adelic Fourier transform
  let T : SAdelicSchwartz F Sf ≃L[ℂ] SAdelicSchwartz F Sf := FG.trans (pullCLE e')
  have hint : ∀ f : SAdelicSchwartz F Sf, Integrable f.eval ν := fun f => (hFG f).1
  have hT : ∀ f : SAdelicSchwartz F Sf, (T f).eval = sLocalFourier Sf f.eval := by
    intro f
    funext y
    have h := (hFG f).2 (e' (Multiplicative.ofAdd y))
    show (FG f).toFun (e' (Multiplicative.ofAdd y)) = _
    refine h.trans ?_
    unfold RiemannMasullo.lcaFourier sLocalFourier
    congr 1
    funext x
    exact congrArg (fun z => f.toFun x * z) (he' (Multiplicative.toAdd x) y)
  -- Fourier transforms of integrable functions are continuous
  have hcontF : ∀ φ : SAdeleRing F Sf → ℂ, Integrable φ ν → Continuous (sLocalFourier Sf φ) := by
    intro φ hφ
    unfold sLocalFourier
    refine continuous_of_dominated (bound := fun x => ‖φ x‖) (fun y => ?_) (fun y => ?_)
      hφ.norm (ae_of_all _ fun x => ?_)
    · exact hφ.aestronglyMeasurable.mul
        (hψc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact ae_of_all _ fun x => by rw [norm_mul, hψn, mul_one]
    · exact continuous_const.mul (hψc.comp (continuous_const.mul continuous_id))
  have hcont : ∀ f : SAdelicSchwartz F Sf, Continuous f.eval := by
    intro f
    have h : f.eval = sLocalFourier Sf (T.symm f).eval := by
      rw [← hT, T.apply_symm_apply]
    rw [h]
    exact hcontF _ (hint _)
  refine ⟨hint, T, hT, fun f x => ?_⟩
  rw [hT, hT]
  have hFint : Integrable (fun y => ∫ x, f.eval x * sStdCharacter Sf (x * y) ∂ν) ν := by
    have := hint (T f)
    rw [hT] at this
    exact this
  exact hinv f.eval (hcont f) (hint f) hFint x
