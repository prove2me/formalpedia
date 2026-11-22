-- Prove2me | solution 2 for MasulloGRH.completedHeckeLFunction_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:36:44.758151+00:00
-- url     : https://prove2.me/submissions/20f892e7-7e1d-41a5-8ee0-f9f90edc3ae5

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_MasulloGRH_exists_ideleClassEquiv_and_localEquivs_of_ringEquiv
import Theorems.Thm_MasulloGRH_archLFactor_eq_of_localComponent_equiv

set_option autoImplicit false

open MasulloGRH NumberField IsDedekindDomain
open scoped WithZero

noncomputable section

private def characterTransport
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (c : IdeleClassGroup F ≃ₜ* IdeleClassGroup K) : HeckeCharacter F ≃* HeckeCharacter K where
  toFun := PontryaginDual.map (c.symm : IdeleClassGroup K →ₜ* IdeleClassGroup F)
  invFun := PontryaginDual.map (c : IdeleClassGroup F →ₜ* IdeleClassGroup K)
  left_inv χ := PontryaginDual.ext fun x => by
    change χ (c.symm (c x)) = χ x
    rw [c.symm_apply_apply]
  right_inv ψ := PontryaginDual.ext fun x => by
    change ψ (c (c.symm x)) = ψ x
    rw [c.apply_symm_apply]
  map_mul' := map_mul (PontryaginDual.map (c.symm : IdeleClassGroup K →ₜ* IdeleClassGroup F))

private theorem characterTransport_apply
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (c : IdeleClassGroup F ≃ₜ* IdeleClassGroup K) (χ : HeckeCharacter F)
    (x : IdeleClassGroup F) : (characterTransport c χ) (c x) = χ x := by
  change χ (c.symm (c x)) = χ x
  rw [c.symm_apply_apply]

private theorem localComponent_div
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x / y) = χ.localComponent v x / χ.localComponent v y := by
  classical
  have hsingle : ideleSingle v (x / y) = ideleSingle v x / ideleSingle v y := by
    let assemble : (InfiniteAdeleRing F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ ≃* IdeleGroup F :=
      MulEquiv.prodUnits.symm
    change assemble (1, finiteIdeleSingle v (x / y)) =
      assemble (1, finiteIdeleSingle v x) / assemble (1, finiteIdeleSingle v y)
    rw [← map_div assemble]
    apply congrArg assemble
    refine Prod.ext (by simp) ?_
    change finiteIdeleSingle v (x / y) = finiteIdeleSingle v x / finiteIdeleSingle v y
    simp only [finiteIdeleSingle, RestrictedProduct.mulSingle_div, map_div] <;> rfl
  unfold HeckeCharacter.localComponent
  rw [hsingle]
  simp only [← QuotientGroup.mk'_apply, map_div, Circle.coe_div]

private theorem localComponent_eq_of_uniformizers
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hu : χ.IsUnramifiedAt v) {x y : (v.adicCompletion F)ˣ}
    (hx : IsUniformizerAt v x) (hy : IsUniformizerAt v y) :
    χ.localComponent v x = χ.localComponent v y := by
  unfold IsUniformizerAt at hx hy
  have hval : Valued.v ((↑(x / y) : v.adicCompletion F)) = 1 := by
    rw [Units.val_div_eq_div_val, map_div₀, hx, hy, div_self WithZero.exp_ne_zero]
  have hdiv := hu (x / y) hval
  rw [localComponent_div] at hdiv
  have hy₀ : χ.localComponent v y ≠ 0 := Circle.coe_ne_zero _
  exact ((div_eq_iff hy₀).mp hdiv).trans (one_mul _)

private theorem primeValue_eq_of_localComponent_equiv
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion F ≃+* w.adicCompletion K)
    (hval : ∀ x : v.adicCompletion F, Valued.v (a x) = (Valued.v x : ℤᵐ⁰))
    (hlocal : ∀ x : (v.adicCompletion F)ˣ,
      χ.localComponent v x = ψ.localComponent w (Units.map a.toMonoidHom x)) :
    χ.primeValue v = ψ.primeValue w := by
  classical
  let b : (v.adicCompletion F)ˣ ≃* (w.adicCompletion K)ˣ := Units.mapEquiv a.toMulEquiv
  have hvaluation (x : (v.adicCompletion F)ˣ) :
      Valued.v ((b x : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
        (Valued.v (x : v.adicCompletion F) : ℤᵐ⁰) := hval x
  have hunramified : χ.IsUnramifiedAt v ↔ ψ.IsUnramifiedAt w := by
    constructor
    · intro h y hy
      obtain ⟨x, rfl⟩ := b.surjective y
      exact (hlocal x).symm.trans (h x ((hvaluation x).symm.trans hy))
    · intro h x hx
      exact (hlocal x).trans (h (b x) ((hvaluation x).trans hx))
  have huniformizer (x : (v.adicCompletion F)ˣ) :
      IsUniformizerAt w (b x) ↔ IsUniformizerAt v x := by
    unfold IsUniformizerAt
    rw [hvaluation]
  have hp : (χ.IsUnramifiedAt v ∧ ∃ x, IsUniformizerAt v x) ↔
      (ψ.IsUnramifiedAt w ∧ ∃ y, IsUniformizerAt w y) := by
    refine and_congr hunramified ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      exact ⟨b x, (huniformizer x).2 hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := b.surjective y
      exact ⟨x, (huniformizer x).1 hy⟩
  unfold HeckeCharacter.primeValue
  by_cases h : χ.IsUnramifiedAt v ∧ ∃ x, IsUniformizerAt v x
  · have h' := hp.mp h
    rw [dif_pos h, dif_pos h']
    exact (hlocal h.2.choose).trans
      (localComponent_eq_of_uniformizers ψ w h'.1
        ((huniformizer _).2 h.2.choose_spec) h'.2.choose_spec)
  · rw [dif_neg h, dif_neg (fun h' => h (hp.mpr h'))]

private theorem absNorm_eq_of_ringEquiv
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (e : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal =
      Ideal.absNorm ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)) v).asIdeal := by
  let r := RingOfIntegers.mapRingEquiv e
  let w := HeightOneSpectrum.equivOfRingEquiv r v
  have hw : w.asIdeal = v.asIdeal.map r := Ideal.comap_symm r
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal w.asIdeal r hw).toEquiv

private theorem heckeLFunction_eq_of_eulerProduct_eq
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (ψ : HeckeCharacter K) (h : heckeEulerProduct χ = heckeEulerProduct ψ) :
    heckeLFunction χ = heckeLFunction ψ := by
  classical
  exact congrArg (fun E : ℂ → ℂ =>
    if hE : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
        ∀ s : ℂ, 1 < s.re → L s = E s then hE.choose else 0) h

theorem solution
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    (e : F ≃+* K) :
    ∃ transport : HeckeCharacter F ≃* HeckeCharacter K,
      ∀ χ : HeckeCharacter F,
        completedHeckeLFunction χ = completedHeckeLFunction (transport χ) := by
  classical
  let p := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)
  obtain ⟨c, w, finite, infinite, hval, hfinite, hreal, hemb, hinfinite⟩ :=
    exists_ideleClassEquiv_and_localEquivs_of_ringEquiv F K e
  refine ⟨characterTransport c, fun χ => ?_⟩
  let ψ := characterTransport c χ
  have hprime (v : HeightOneSpectrum (𝓞 F)) : χ.primeValue v = ψ.primeValue (p v) := by
    apply primeValue_eq_of_localComponent_equiv χ ψ v (p v) (finite v) (hval v)
    intro x
    unfold HeckeCharacter.localComponent
    rw [← hfinite v x, characterTransport_apply]
  have heuler : heckeEulerProduct χ = heckeEulerProduct ψ := by
    funext s
    unfold heckeEulerProduct
    rw [← p.tprod_eq]
    congr 1
    funext v
    rw [hprime v, absNorm_eq_of_ringEquiv e v]
  have hgamma : χ.gammaFactor = ψ.gammaFactor := by
    funext s
    unfold HeckeCharacter.gammaFactor
    apply Fintype.prod_equiv w
    intro v
    have hlocal (x : (v.Completion)ˣ) :
        χ.localComponentInfinite v x =
          ψ.localComponentInfinite (w v) (Units.map (infinite v).toMonoidHom x) := by
      unfold HeckeCharacter.localComponentInfinite
      rw [← hinfinite v x, characterTransport_apply]
    exact congrFun (archLFactor_eq_of_localComponent_equiv χ ψ v (w v) (infinite v)
      (hreal v) (hemb v) hlocal) s
  change completedHeckeLFunction χ = completedHeckeLFunction ψ
  unfold completedHeckeLFunction
  rw [hgamma, heckeLFunction_eq_of_eulerProduct_eq χ ψ heuler]
