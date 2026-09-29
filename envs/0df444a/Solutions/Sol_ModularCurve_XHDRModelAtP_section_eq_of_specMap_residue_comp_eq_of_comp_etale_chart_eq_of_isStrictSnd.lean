-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1a874105-4988-5234-8723-30c579227c65

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups
open TensorProduct

universe u

namespace SecUniq

theorem rigid
    {P E B : Type*} [CommRing P] [CommRing E] [CommRing B] [Algebra P E] [Algebra P B]
    [Algebra.FormallyUnramified P E] [Algebra.EssFiniteType P E] [IsLocalRing B]
    (φ ψ : E →ₐ[P] B) (h : ∀ x : E, φ x - ψ x ∈ IsLocalRing.maximalIdeal B) : φ = ψ := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal P E = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg P E)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[E⁄P]
  let χ : E ⊗[P] E →ₐ[P] B := Algebra.TensorProduct.productMap φ ψ
  have hres : ∀ b : E, IsLocalRing.residue B (ψ b) = IsLocalRing.residue B (φ b) := fun b => by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub, Ideal.neg_mem_iff]
    exact h b

  have key : ∀ z : E ⊗[P] E,
      IsLocalRing.residue B (χ z) = IsLocalRing.residue B (φ (Algebra.TensorProduct.lmul' P (S := E) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul, map_mul,
        map_mul, hres b]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  have hχe : χ e = 0 := by
    have hmem : χ e ∈ IsLocalRing.maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, key, RingHom.mem_ker.mp (hsp ▸ Ideal.mem_span_singleton_self e :
        e ∈ KaehlerDifferential.ideal P E), map_zero, map_zero]
    have hid : IsIdempotentElem (χ e) := he.map χ
    have hu : IsUnit (1 - χ e) :=
      (IsLocalRing.isUnit_or_isUnit_one_sub_self (χ e)).resolve_left (IsLocalRing.mem_maximalIdeal _ |>.mp hmem)
    have hz : χ e * (1 - χ e) = 0 := by rw [mul_sub, mul_one, hid.eq, sub_self]
    exact hu.mul_left_eq_zero.mp hz
  ext a
  have hmem := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal P a
  rw [hsp] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have h0 : χ ((1 : E) ⊗ₜ[P] a - a ⊗ₜ[P] (1 : E)) = 0 := by rw [← hc, map_mul, hχe, mul_zero]
  rw [map_sub, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul, map_one,
    map_one, one_mul, mul_one, sub_eq_zero] at h0
  exact h0.symm

theorem affine_core {A : Type u} [CommRing A] [IsLocalRing A] {V W : Scheme.{u}} [IsAffine V] [IsAffine W]
    (g : V ⟶ W) [Etale g] (t t' : Spec (CommRingCat.of A) ⟶ V)
    (h1 : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ t =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ t')
    (h2 : t ≫ g = t' ≫ g) : t = t' := by
  have hget : RingHom.Etale g.appTop.hom := HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale) g inferInstance
  letI alg : Algebra Γ(W, ⊤) Γ(V, ⊤) := g.appTop.hom.toAlgebra
  haveI : Algebra.Etale Γ(W, ⊤) Γ(V, ⊤) := hget
  let toA : Γ(Spec (CommRingCat.of A), ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
  have toA_inj : Function.Injective toA := by
    intro x y hxy
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hxy
    simpa [toA, ← CommRingCat.comp_apply] using this
  letI algA : Algebra Γ(W, ⊤) A := (toA.comp (t ≫ g).appTop.hom).toAlgebra
  let φ : Γ(V, ⊤) →ₐ[Γ(W, ⊤)] A :=
    { toRingHom := toA.comp t.appTop.hom
      commutes' := fun r => by
        show toA (t.appTop.hom (g.appTop.hom r)) = toA ((t ≫ g).appTop.hom r)
        rw [Scheme.Hom.comp_appTop]; rfl }
  let ψ : Γ(V, ⊤) →ₐ[Γ(W, ⊤)] A :=
    { toRingHom := toA.comp t'.appTop.hom
      commutes' := fun r => by
        show toA (t'.appTop.hom (g.appTop.hom r)) = toA ((t ≫ g).appTop.hom r)
        rw [h2, Scheme.Hom.comp_appTop]; rfl }

  have natp : ∀ y : Γ(Spec (CommRingCat.of A), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField A))).hom.hom
        ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).appTop.hom y) = IsLocalRing.residue A (toA y) := by
    intro y
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue A))
    have h := congrArg (fun k => k.hom y) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  have hφψ : ∀ x, φ x - ψ x ∈ IsLocalRing.maximalIdeal A := by
    intro x
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    show IsLocalRing.residue A (toA (t.appTop.hom x)) = IsLocalRing.residue A (toA (t'.appTop.hom x))
    have e := congrArg Scheme.Hom.appTop h1
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e
    have ex := CategoryTheory.ConcreteCategory.congr_hom e x
    rw [← natp, ← natp]
    exact congrArg _ ex
  have hφψeq : φ = ψ := rigid φ ψ hφψ
  have happ : t.appTop = t'.appTop := by
    ext x
    exact toA_inj (AlgHom.congr_fun hφψeq x)
  rw [← cancel_mono V.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]

theorem main {A : Type u} [CommRing A] [IsLocalRing A] {U Y : Scheme.{u}} (f : U ⟶ Y) [Etale f]
    (s s' : Spec (CommRingCat.of A) ⟶ U)
    (h1 : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s')
    (h2 : s ≫ f = s' ≫ f) : s = s' := by
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue A)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue A))
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom (IsLocalRing.residue A))
  have hy : s'.base (IsLocalRing.closedPoint A) = s.base (IsLocalRing.closedPoint A) := by
    have := congrArg (fun k => k.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))) h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app, hpt] at this
    exact this.symm
  obtain ⟨_, ⟨W, hW, rfl⟩, hW1, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base (s.base (IsLocalRing.closedPoint A)))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hV1, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show s.base (IsLocalRing.closedPoint A) ∈ (f ⁻¹ᵁ W : Set U) from hW1)
      (f ⁻¹ᵁ W).isOpen
  have hle : V ≤ f ⁻¹ᵁ W := hVW
  have hsV : s ⁻¹ᵁ V = ⊤ := (IsLocalRing.closedPoint_mem_iff _).mp hV1
  have hs'V : s' ⁻¹ᵁ V = ⊤ := (IsLocalRing.closedPoint_mem_iff _).mp (show s'.base (IsLocalRing.closedPoint A) ∈ V by rw [hy]; exact hV1)
  have hr : Set.range s.base ⊆ Set.range (Scheme.Opens.ι V).base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show x ∈ s ⁻¹ᵁ V
    rw [hsV]; trivial
  have hr' : Set.range s'.base ⊆ Set.range (Scheme.Opens.ι V).base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show x ∈ s' ⁻¹ᵁ V
    rw [hs'V]; trivial
  have ht := IsOpenImmersion.lift_fac (Scheme.Opens.ι V) s hr
  have ht' := IsOpenImmersion.lift_fac (Scheme.Opens.ι V) s' hr'
  haveI : IsAffine V := hV
  haveI : IsAffine W := hW
  have h2' : IsOpenImmersion.lift (Scheme.Opens.ι V) s hr ≫ f.resLE W V hle = IsOpenImmersion.lift (Scheme.Opens.ι V) s' hr' ≫ f.resLE W V hle := by
    rw [← cancel_mono (Scheme.Opens.ι W), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ht,
      ← Category.assoc, ht', h2]
  have h1' : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ IsOpenImmersion.lift (Scheme.Opens.ι V) s hr =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ IsOpenImmersion.lift (Scheme.Opens.ι V) s' hr' := by
    rw [← cancel_mono (Scheme.Opens.ι V), Category.assoc, Category.assoc, ht, ht', h1]
  have key := affine_core (f.resLE W V hle) _ _ h1' h2'
  rw [← ht, ← ht', key]

end SecUniq

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base)

    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _)
    (het : Etale f)
    (hpt : f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A))
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ s s' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → s' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →

      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s' →
      s ≫ f = s' ≫ f → s = s' := by
  intro s s' _ _ h1 h2
  haveI := het
  exact SecUniq.main f s s' h1 h2

end S_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd (solution)
