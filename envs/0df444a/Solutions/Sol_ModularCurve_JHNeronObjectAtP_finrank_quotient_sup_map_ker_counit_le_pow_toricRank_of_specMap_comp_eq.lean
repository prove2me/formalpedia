-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c347169f-1ed4-5738-bcf9-1558c69bef1d

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre
import Theorems.Thm_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

section HRN2support
open ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard

namespace HRN2

theorem isFinite_and_iso_muScheme_and_finrank_schemeKer_torus
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI KL := RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA))
      O.abqFibre (fun i => O.abqFibre_mul i)
    IsFinite (KL.schemeKerStr m) ∧
    (∃ e' : KL.schemeKer m ≅ AlgebraicGeometry.SplitTorus.muScheme (ResidueField ↥A) O.toricRank m,
      e'.hom ≫ AlgebraicGeometry.SplitTorus.muStr (ResidueField ↥A) O.toricRank m = KL.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (KL.schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ(KL.schemeKer m, ⊤) = m ^ O.toricRank) := by
  obtain ⟨e, he, hen⟩ := JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre p M H hpM A hA Λ hΛ O
  refine AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme O.toricRank
    (RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre) _ e ?_ hen m hm
  show e.hom ≫ (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre ≫ _) = _
  rw [← Category.assoc, he]
  exact O.torusFibre.2

theorem finrank_le_of_isClosedImmersion_of_isFinite
    {κ : Type} [Field κ] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of κ)) [IsFinite f]
    (Q : Type) [CommRing Q] [Algebra κ Q]
    (z : Spec (CommRingCat.of Q) ⟶ X) [IsClosedImmersion z]
    (hz : z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap κ Q))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    Module.finrank κ Q ≤ Module.finrank κ Γ(X, ⊤) := by
  have hX := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := f)).mp ‹_›
  haveI : IsAffine X := hX.1
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine z
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app _

  haveI : Module.Finite κ Γ(X, ⊤) := by
    have h1 : ((Scheme.ΓSpecIso (.of κ)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.Finite := by
      rw [happ, CommRingCat.hom_comp]
      exact RingHom.Finite.comp hX.2
        (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of κ)).inv).2)
    exact h1

  have hcomp : (Scheme.ΓSpecIso (.of κ)).inv ≫ f.appTop ≫ z.appTop ≫ (Scheme.ΓSpecIso (.of Q)).hom =
      CommRingCat.ofHom (algebraMap κ Q) := by
    rw [← Scheme.Hom.comp_appTop_assoc, hz, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

  let φ : Γ(X, ⊤) →ₐ[κ] Q :=
    { ((Scheme.ΓSpecIso (.of Q)).hom.hom.comp z.appTop.hom) with
      commutes' := fun r => by
        show ((((Scheme.ΓSpecIso (.of κ)).inv ≫ f.appLE ⊤ ⊤ le_top) ≫ z.appTop ≫ (Scheme.ΓSpecIso (.of Q)).hom).hom r) = algebraMap κ Q r
        rw [happ, Category.assoc, hcomp]
        rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Q)).hom).2.comp hsurj
  exact LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hφ

theorem isClosedImmersion_lift_baseChange
    {X S : Scheme.{0}} (g : X ⟶ S) {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (b : Spec (CommRingCat.of R) ⟶ S) (c : Spec (CommRingCat.of K) ⟶ S)
    (hc : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b = c)
    (A₁ : Type) [CommRing A₁] [Algebra R A₁] (i : Spec (CommRingCat.of A₁) ⟶ X)
    (hi : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R A₁)) ≫ b)
    [IsClosedImmersion (pullback.lift (f := g) (g := b) i (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) hi)]
    (h2 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A₁))) ≫ c) :
    IsClosedImmersion (pullback.lift (f := g) (g := c)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i)
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A₁)))) h2) := by

  have h₁ : pullback.lift (f := g) (g := b) i (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) hi ≫ pullback.snd g b =
      Spec.map (CommRingCat.ofHom (algebraMap R A₁)) := pullback.lift_snd _ _ _
  have halg : (algebraMap K (K ⊗[R] A₁)) = (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A₁) :=
    RingHom.ext fun _ => rfl

  have hsq : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫
        pullback.lift (f := g) (g := b) i (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) hi) ≫ pullback.snd g b =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A₁)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [Category.assoc, h₁, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    change (1 : K) ⊗ₜ[R] algebraMap R A₁ r = algebraMap R K r ⊗ₜ[R] (1 : A₁)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hpb : IsPullback
      (pullback.lift (f := pullback.snd g b) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) _ _ hsq)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)))
      (pullback.fst (pullback.snd g b) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (pullback.lift (f := g) (g := b) i (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) hi) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (pullback.snd g b) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).flip
    rw [pullback.lift_snd, h₁]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K A₁)
  haveI : IsClosedImmersion
      (pullback.lift (f := pullback.snd g b) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) _ _ hsq) :=
    MorphismProperty.of_isPullback hpb.flip ‹_›

  have key : pullback.lift (f := g) (g := c)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i)
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A₁)))) h2 =
      pullback.lift (f := pullback.snd g b) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) _ _ hsq ≫
        (pullbackLeftPullbackSndIso g b (Spec.map (CommRingCat.ofHom (algebraMap R K)))).hom ≫
          (pullback.congrHom rfl hc).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd, halg]
  rw [key]
  infer_instance

theorem exists_isClosedImmersion_baseChange
    {X S : Scheme.{0}} (g : X ⟶ S) {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (b : Spec (CommRingCat.of R) ⟶ S) (c : Spec (CommRingCat.of K) ⟶ S)
    (hc : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b = c)
    (A₁ : Type) [CommRing A₁] [Algebra R A₁] (i : Spec (CommRingCat.of A₁) ⟶ X)
    (hi : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R A₁)) ≫ b)
    [IsClosedImmersion (pullback.lift (f := g) (g := b) i (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) hi)] :
    ∃ x : Spec (CommRingCat.of (K ⊗[R] A₁)) ⟶ pullback g c,
      IsClosedImmersion x ∧
      x ≫ pullback.fst g c =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i ∧
      x ≫ pullback.snd g c = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A₁))) := by
  have halg : (algebraMap K (K ⊗[R] A₁)) = (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A₁) :=
    RingHom.ext fun _ => rfl
  have h2 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A₁))) ≫ c := by
    rw [Category.assoc, hi, ← hc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg]
    congr 2
    ext r
    change (1 : K) ⊗ₜ[R] algebraMap R A₁ r = algebraMap R K r ⊗ₜ[R] (1 : A₁)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  exact ⟨_, isClosedImmersion_lift_baseChange g b c hc A₁ i hi h2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end HRN2

end HRN2support

namespace FKKerOrd

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section RGL

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem nsmul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h, GoodReductionJacobian.schemeHomOverComp_coe]
  rfl

noncomputable def kerLift {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f)
    (hx : G.nsmul t n x = G.one t) : T ⟶ G.schemeKer n :=
  pullback.lift x.1 t (by rw [← nsmul_coe, hx, RelativeGroupLaw.one_coe_eq])

@[scoped simp] theorem kerLift_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f)
    (hx : G.nsmul t n x = G.one t) : kerLift G t n x hx ≫ pullback.fst _ _ = x.1 :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem kerLift_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f)
    (hx : G.nsmul t n x = G.one t) : kerLift G t n x hx ≫ G.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

theorem baseChangePointToBase_nsmul {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul (t' ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.baseChangePointToBase_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f)
    (h : G.mul t a a = a) : a = G.one t := by
  have h2 := congrArg (fun z => G.mul t z (G.inv t a)) h
  beta_reduce at h2
  rw [G.mul_assoc, G.mul_inv_cancel, G.mul_one] at h2
  exact h2

end RGL

end FKKerOrd
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq.FKKerOrd"

namespace FKKerOrd

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem baseChange_one_fst {p : ℕ} {X : Scheme.{0}} (f : X ⟶ base p) (L : RelativeGroupLaw (baseRing p) f)
    {R' : Type} [CommRing R'] (ιb : Spec (CommRingCat.of R') ⟶ base p) :
    ((L.baseChange ιb).one (𝟙 _)).1 ≫ pullback.fst f ιb = ιb ≫ (L.one (𝟙 _)).1 := by
  rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
    RelativeGroupLaw.one_coe_eq, Category.id_comp]

theorem core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ) (hΛf : IsProper Λ.f)
    {Gv G' A' : Type} [CommRing Gv] [CommRing G'] [Algebra (ZMod p) G'] [CommRing A'] [Algebra (ZMod p) A']
    (v : ℕ)
    (ιv : Spec (CommRingCat.of Gv) ⟶ O.G)
    (hιp : ιv ≫ O.L.schemeNsmul (p ^ v) = (ιv ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)
    (ιpv : Spec (CommRingCat.of G') ⟶ pullback O.g σp) [IsClosedImmersion ιpv]
    (incR : Gv →+* G')
    (hιp₁ : ιpv ≫ pullback.fst O.g σp = Spec.map (CommRingCat.ofHom incR) ≫ ιv)
    (hιp₂ : ιpv ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) G')))
    (q : Fin 2 → NeronModelInfra.SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    [Algebra (ZMod p) (ResidueField ↥Pl)]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) ≫ σp = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)
    (ι'v : Spec (CommRingCat.of A') ⟶ pullback Λ.f σp)
    (ε : A' →ₐ[ZMod p] ZMod p)
    (hU : Spec.map (CommRingCat.ofHom (ε : A' →+* ZMod p)) ≫ ι'v = ((Λ.L.baseChange σp).one (𝟙 _)).1)
    (φ : Fin 2 → (A' →ₐ[ZMod p] G'))
    (hφ : ∀ i : Fin 2, Spec.map (CommRingCat.ofHom (φ i : A' →+* G')) ≫ ι'v = ιpv ≫ (q i).1)
    (J : Ideal G') (hJ : ∀ i : Fin 2, Ideal.map (φ i) (RingHom.ker ε) ≤ J) :
    Module.finrank (ZMod p) (G' ⧸ J) ≤ p ^ (v * O.toricRank) := by
  classical
  haveI : IsSeparated Λ.f := inferInstance
  haveI : IsSeparated O.g := O.separated

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective
  have halg : (Ideal.Quotient.mk J).comp (algebraMap (ZMod p) G') = algebraMap (ZMod p) (G' ⧸ J) :=
    RingHom.ext fun _ => rfl
  have hi3g : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv) ≫ pullback.fst O.g σp) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J))) ≫ σp := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ιpv, hιp₂, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, halg]
  have hlift3 : pullback.lift (f := O.g) (g := σp) ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv) ≫ pullback.fst O.g σp)
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J)))) hi3g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, hιp₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]
  haveI : IsClosedImmersion (pullback.lift (f := O.g) (g := σp)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv) ≫ pullback.fst O.g σp)
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J)))) hi3g) := by
    rw [hlift3]; infer_instance
  obtain ⟨xV, hxVcl, hxV1, hxV2⟩ := HRN2.exists_isClosedImmersion_baseChange O.g σp (resPt Pl ≫ Λ.σA) hfac (G' ⧸ J)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv) ≫ pullback.fst O.g σp) hi3g
  haveI := hxVcl

  obtain ⟨tV, htV⟩ : ∃ tV, tV = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J)))) := ⟨_, rfl⟩
  rw [← htV] at hxV2
  let xVpt : SchemeHomOver tV (RelativeGroupLaw.baseChangeStr (resPt Pl ≫ Λ.σA) O.g) := ⟨xV, hxV2⟩
  have hr : (algebraMap (ZMod p) (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) =
      (algebraMap (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))).comp (algebraMap (ZMod p) (ResidueField ↥Pl)) :=
    IsScalarTower.algebraMap_eq _ _ _
  have hr2 : (Algebra.TensorProduct.includeRight.toRingHom : G' ⧸ J →+* ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J)).comp (algebraMap (ZMod p) (G' ⧸ J)) =
      algebraMap (ZMod p) (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J)) :=
    RingHom.ext fun x => (Algebra.TensorProduct.includeRight (R := ZMod p) (A := ResidueField ↥Pl) (B := G' ⧸ J)).commutes x
  have htVfac : tV ≫ (resPt Pl ≫ Λ.σA) =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G' ⧸ J →+* ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J)))) ≫ σp := by
    rw [htV, ← hfac, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← hr, hr2]

  have hring : ∀ i : Fin 2, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom (φ i : A' →+* G')) =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J))) ≫ Spec.map (CommRingCat.ofHom (ε : A' →+* ZMod p)) := by
    intro i
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    have hmem : φ i a - algebraMap (ZMod p) G' (ε a) ∈ J := by
      have ha : a - algebraMap (ZMod p) A' (ε a) ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
        exact sub_eq_zero.mpr rfl
      have h1 : φ i (a - algebraMap (ZMod p) A' (ε a)) ∈ Ideal.map (φ i) (RingHom.ker ε) := Ideal.mem_map_of_mem _ ha
      rw [map_sub, AlgHom.commutes] at h1
      exact hJ i h1
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [← Ideal.Quotient.mk_algebraMap]
    exact Ideal.Quotient.eq.2 hmem

  have hxVmap : xV ≫ pullback.map O.g (resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G' ⧸ J →+* ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ιpv := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hxV1, Category.comp_id, Category.assoc, Category.assoc, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hxV2, htV, Category.assoc, Category.assoc, hιp₂, ← Spec.map_comp,
        ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg, hr2, hr]
  have hx : ∀ i : Fin 2, NeronModelInfra.schemeHomOverComp xVpt (O.abqFibre i) = (Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one tV := by
    intro i
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.one_coe_eq]
    change xV ≫ (O.abqFibre i).1 = tV ≫ _
    apply pullback.hom_ext
    ·
      have hA : pullback.fst Λ.f (resPt Pl ≫ Λ.σA) =
          pullback.map Λ.f (resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ pullback.fst Λ.f σp := by
        rw [pullback.lift_fst, Category.comp_id]
      have e1 : xV ≫ (O.abqFibre i).1 ≫ pullback.fst Λ.f (resPt Pl ≫ Λ.σA) =
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G' ⧸ J →+* ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (G' ⧸ J)))) ≫ σp ≫ (Λ.L.one (𝟙 _)).1 := by
        rw [hA, ← Category.assoc (O.abqFibre i).1, hqbc i, Category.assoc, ← Category.assoc xV, hxVmap, Category.assoc, Category.assoc,
          ← Category.assoc ιpv, ← hφ i, ← Category.assoc (Spec.map _) (Spec.map _ ≫ ι'v), ← Category.assoc (Spec.map _) (Spec.map _) ι'v,
          hring i, Category.assoc, Category.assoc, ← Category.assoc (Spec.map _) ι'v, hU, baseChange_one_fst, Category.assoc]
      rw [Category.assoc, Category.assoc, e1, baseChange_one_fst, ← Category.assoc tV, htVfac]
      simp only [Category.assoc]
    · rw [Category.assoc, Category.assoc]
      rw [show (O.abqFibre i).1 ≫ pullback.snd Λ.f (resPt Pl ≫ Λ.σA) = pullback.snd O.g (resPt Pl ≫ Λ.σA) from (O.abqFibre i).2,
        hxV2, show ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 ≫ pullback.snd Λ.f (resPt Pl ≫ Λ.σA) = 𝟙 _ from
          ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).2, Category.comp_id]

  obtain ⟨zK, hzKdef⟩ : ∃ zK, zK = RelativeGroupLaw.kerPairLift (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre xVpt hx := ⟨_, rfl⟩
  have hzK : zK ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre = xV := by
    rw [hzKdef, RelativeGroupLaw.kerPairLift_ι]
  let zKpt : SchemeHomOver tV (RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre) :=
    ⟨zK, by
      change zK ≫ (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre ≫ pullback.snd O.g (resPt Pl ≫ Λ.σA)) = tV
      rw [← Category.assoc, hzK, hxV2]⟩

  obtain ⟨j, hjdef⟩ : ∃ j : Spec (CommRingCat.of (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) ⟶ Spec (CommRingCat.of Gv),
      j = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G' ⧸ J →+* ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map (CommRingCat.ofHom incR) := ⟨_, rfl⟩
  have htb1 : (RelativeGroupLaw.baseChangePointToBase (resPt Pl ≫ Λ.σA) xVpt).1 = j ≫ ιv := by
    rw [RelativeGroupLaw.baseChangePointToBase_coe, hjdef]
    change xV ≫ pullback.fst O.g (resPt Pl ≫ Λ.σA) = _
    rw [hxV1, Category.assoc, Category.assoc, hιp₁]
    simp only [Category.assoc]
  have hj : j ≫ (ιv ≫ O.g) = tV ≫ (resPt Pl ≫ Λ.σA) := by
    rw [← Category.assoc, ← htb1]; exact (RelativeGroupLaw.baseChangePointToBase (resPt Pl ≫ Λ.σA) xVpt).2
  have hιtors : O.L.nsmul (ιv ≫ O.g) (p ^ v) ⟨ιv, rfl⟩ = O.L.one (ιv ≫ O.g) := by
    apply Subtype.ext
    rw [nsmul_coe, RelativeGroupLaw.one_coe_eq]
    exact hιp
  have htb : RelativeGroupLaw.baseChangePointToBase (resPt Pl ≫ Λ.σA) xVpt = schemeHomOverComp j hj ⟨ιv, rfl⟩ :=
    Subtype.ext (by rw [htb1, GoodReductionJacobian.schemeHomOverComp_coe])
  have htors : (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA)) (Λ.L.baseChange (resPt Pl ≫ Λ.σA))
      O.abqFibre (fun i => O.abqFibre_mul i)).nsmul tV (p ^ v) zKpt =
      (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA)) (Λ.L.baseChange (resPt Pl ≫ Λ.σA))
        O.abqFibre (fun i => O.abqFibre_mul i)).one tV := by
    apply (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre tV).injective
    apply Subtype.ext
    rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, RelativeGroupLaw.kerPairPointEquiv_one]
    have hxe : (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre tV zKpt).1 = xVpt :=
      Subtype.ext hzK
    rw [hxe]
    apply (RelativeGroupLaw.baseChangePointEquiv (resPt Pl ≫ Λ.σA) (f := O.g) tV).injective
    change RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
    rw [baseChangePointToBase_nsmul, RelativeGroupLaw.baseChangePointToBase_one, htb, ← RelativeGroupLaw.nsmul_natural, hιtors,
      RelativeGroupLaw.one_natural]
  obtain ⟨zKer, hzKerdef⟩ : ∃ zKer, zKer = kerLift (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA))
      (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)) tV (p ^ v) zKpt htors := ⟨_, rfl⟩
  have hzKer1 : zKer ≫ pullback.fst _ _ = zK := by rw [hzKerdef, kerLift_fst]
  have hzKer2 : zKer ≫ (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA)) (Λ.L.baseChange (resPt Pl ≫ Λ.σA))
      O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr (p ^ v) = tV := by rw [hzKerdef, kerLift_snd]

  haveI : IsClosedImmersion (((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA))
      (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).one (𝟙 _)).1) :=
    RelativeGroupLaw.isClosedImmersion_one _
  haveI : IsClosedImmersion (zKer ≫ (pullback.fst _ _ ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre)) := by
    rw [← Category.assoc, hzKer1, hzK]; exact hxVcl
  have hzcl : IsClosedImmersion zKer :=
    IsClosedImmersion.of_comp zKer (pullback.fst _ _ ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) O.abqFibre)

  obtain ⟨hF, -, hrank⟩ := HRN2.isFinite_and_iso_muScheme_and_finrank_schemeKer_torus p M H hpM Pl hPl Λ hΛf O (p ^ v)
    (pow_pos (Fact.out : p.Prime).pos v)
  haveI := hF
  haveI := hzcl
  have hle := HRN2.finrank_le_of_isClosedImmersion_of_isFinite
    ((RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt Pl ≫ Λ.σA)) (Λ.L.baseChange (resPt Pl ≫ Λ.σA))
      O.abqFibre (fun i => O.abqFibre_mul i)).schemeKerStr (p ^ v))
    (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J)) zKer (hzKer2.trans htV)
  have hbc : Module.finrank (ResidueField ↥Pl) (ResidueField ↥Pl ⊗[ZMod p] (G' ⧸ J)) = Module.finrank (ZMod p) (G' ⧸ J) := Module.finrank_baseChange
  rw [← hbc, pow_mul]
  exact hle.trans hrank.le

end FKKerOrd
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq.FKKerOrd"

open ModularCurve ModularCurve.JZeroNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hΛf : IsProper Λ.f)

    (Rh : Type) [CommRing Rh] [Algebra Rh (ZMod p)]
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)

    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)
    (hσp : Spec.map (CommRingCat.ofHom (algebraMap Rh (ZMod p))) ≫ Spec.map (CommRingCat.ofHom ρh) = σp)
    (ιp : ∀ v : ℕ, Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback O.g σp)
    (hιp₁ : ∀ v : ℕ, ιp v ≫ pullback.fst O.g σp =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι v)
    (hιp₂ : ∀ v : ℕ, ιp v ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (q : Fin 2 → NeronModelInfra.SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))

    [Algebra (ZMod p) (ResidueField ↥Pl)]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) ≫ σp = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : NeronModelInfra.SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)

    {hΛ : ℕ} (𝒜 : PDivisibleGroup (ModularCurve.JZeroNeronObjectAtP.baseRing p) p hΛ)
    [Algebra (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p)]
    (hσp' : σp = Spec.map (CommRingCat.ofHom (algebraMap (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p))))
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))

    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
        ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)
    :
    ∀ (v : ℕ) (φ : Fin 2 → ((𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)),
      (∀ i : Fin 2, Spec.map (CommRingCat.ofHom (φ i : (𝒜.baseChange (ZMod p)).level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι' v = ιp v ≫ (q i).1) →
      Module.finrank (ZMod p) ((ZMod p ⊗[Rh] 𝒢.level v) ⧸
        (Ideal.map (φ 0) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v))) ⊔
          Ideal.map (φ 1) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))) ≤
        p ^ (v * O.toricRank) := by
  intro v φ hφ

  haveI : IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
      (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) (hιbase v)) := hιcl v (hιbase v)
  obtain ⟨x1, hx1cl, hx11, hx12⟩ := HRN2.exists_isClosedImmersion_baseChange O.g (Spec.map (CommRingCat.ofHom ρh)) σp hσp
    (𝒢.level v) (ι v) (hιbase v)
  have hx1eq : x1 = ιp v := by
    apply pullback.hom_ext
    · rw [hx11, hιp₁]
    · rw [hx12, hιp₂]
  haveI : IsClosedImmersion (ιp v) := hx1eq ▸ hx1cl

  have hco : ((PDivisibleGroup.Point.toAlgHom (1 : (𝒜.baseChange (ZMod p)).Point (ZMod p) v) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p) :
      (𝒜.baseChange (ZMod p)).level v →+* ZMod p) = (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p) :=
    RingHom.ext fun a => by
      rw [RingHom.coe_coe, RingHom.coe_coe, PDivisibleGroup.Point.one_apply, Bialgebra.counitAlgHom_apply]; rfl
  have hU : Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p)) ≫ ι' v =
      ((Λ.L.baseChange σp).one (𝟙 _)).1 := by
    rw [← hco]
    have hx1 : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : (𝒜.baseChange (ZMod p)).Point (ZMod p) v) :
        (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))) := by
      rw [Category.assoc, hι'base, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.coe_coe]; exact AlgHom.commutes _ x
    have hm := hι'mul v (ZMod p) 1 1 hx1 hx1
    rw [mul_one] at hm
    have hpt : (⟨_, hx1⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))))
        (RelativeGroupLaw.baseChangeStr σp Λ.f)) = (Λ.L.baseChange σp).one _ :=
      FKKerOrd.eq_one_of_mul_self _ _ _ (Subtype.ext hm).symm
    have hs1 : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))) = 𝟙 _ := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    have h2 : Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : (𝒜.baseChange (ZMod p)).Point (ZMod p) v) :
        (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p) : (𝒜.baseChange (ZMod p)).level v →+* ZMod p)) ≫ ι' v =
        ((Λ.L.baseChange σp).one (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p))))).1 := congrArg Subtype.val hpt
    rw [RelativeGroupLaw.one_coe_eq, hs1, Category.id_comp] at h2
    exact h2

  exact FKKerOrd.core p M H hpM Pl hPl Λ O hΛf v (ι v) (hιp v) σp (ιp v)
    (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v) (hιp₁ v) (hιp₂ v) q hfac hqbc (ι' v)
    (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v)) hU φ hφ _
    (fun i => by
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right)

end S_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq (solution)
