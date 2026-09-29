-- Prove2me | solution 1 for ModularCurve.exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/71ee2cdf-8228-5de7-8dc2-644f6bc88efc

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
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace HBC

open WithConv

section ConvAlgebra

variable {S : Type} [CommRing S] {A : Type} [CommRing A] [Bialgebra S A]

theorem lmul'_comp_map_includeLeft_includeRight :
    (Algebra.TensorProduct.lmul' S (S := A ⊗[S] A)).comp
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A)
        (Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A)) = AlgHom.id S (A ⊗[S] A) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, AlgHom.id_apply]

theorem convMul_includeLeft_includeRight :
    (toConv (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A) *
      toConv (Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A)).ofConv = Bialgebra.comulAlgHom S A := by
  rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc, lmul'_comp_map_includeLeft_includeRight, AlgHom.id_comp]

variable {C : Type} [CommRing C] [Bialgebra S C]

theorem map_comp_comul_of_forall_convMul (θ : C ≃ₐ[S] A)
    (hθ : ∀ (B : Type) [CommRing B] [Algebra S B] (x y : A →ₐ[S] B),
      toConv (x.comp (θ : C →ₐ[S] A)) * toConv (y.comp (θ : C →ₐ[S] A)) = toConv ((toConv x * toConv y).ofConv.comp (θ : C →ₐ[S] A))) :
    (Algebra.TensorProduct.map (θ : C →ₐ[S] A) (θ : C →ₐ[S] A)).comp (Bialgebra.comulAlgHom S C) =
      (Bialgebra.comulAlgHom S A).comp (θ : C →ₐ[S] A) := by
  have h := hθ (A ⊗[S] A) Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  calc (Algebra.TensorProduct.map (θ : C →ₐ[S] A) (θ : C →ₐ[S] A)).comp (Bialgebra.comulAlgHom S C)
      = ((Algebra.TensorProduct.lmul' S (S := A ⊗[S] A)).comp
          (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A)
            (Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A))).comp
          ((Algebra.TensorProduct.map (θ : C →ₐ[S] A) (θ : C →ₐ[S] A)).comp (Bialgebra.comulAlgHom S C)) := by
        rw [lmul'_comp_map_includeLeft_includeRight, AlgHom.id_comp]
    _ = (toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A).comp (θ : C →ₐ[S] A)) *
          toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).comp (θ : C →ₐ[S] A))).ofConv := by
        rw [AlgHom.convMul_def, ofConv_toConv, Algebra.TensorProduct.map_comp]
        simp only [AlgHom.comp_assoc]
    _ = (toConv (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A) *
          toConv (Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A)).ofConv.comp (θ : C →ₐ[S] A) := by
        rw [h, ofConv_toConv]
    _ = (Bialgebra.comulAlgHom S A).comp (θ : C →ₐ[S] A) := by rw [convMul_includeLeft_includeRight]

end ConvAlgebra

section Restrict

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {C : Type} [CommRing C] [Bialgebra R C]
  {B : Type} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

noncomputable abbrev restr (x : S ⊗[R] C →ₐ[S] B) : C →ₐ[R] B :=
  (x.restrictScalars R).comp (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C)

@[scoped simp] theorem restr_apply (x : S ⊗[R] C →ₐ[S] B) (c : C) : restr x c = x ((1 : S) ⊗ₜ[R] c) := rfl

theorem eq_of_restr_eq {x y : S ⊗[R] C →ₐ[S] B} (h : restr x = restr y) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact h

theorem restr_convMul (x y : S ⊗[R] C →ₐ[S] B) :
    restr (toConv x * toConv y).ofConv = (toConv (restr x) * toConv (restr y)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [restr_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  obtain ⟨ι, t, f, g, hrep⟩ :=
    (⟨_, _, _, _, (Coalgebra.Repr.arbitrary R c).eq⟩ :
      ∃ (ι : Type) (t : Finset ι) (f g : ι → C), ∑ i ∈ t, f i ⊗ₜ[R] g i = Coalgebra.comul (R := R) c)
  rw [← hrep, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul]
  rfl

end Restrict

section PointsBialg

variable {S : Type} [CommRing S] {p h₁ h₂ : ℕ} (G₁ : PDivisibleGroup S p h₁) (G₂ : PDivisibleGroup S p h₂) (v w : ℕ)

noncomputable def bialgEquivOfConvMul (θ : G₂.level w ≃ₐ[S] G₁.level v)
    (hθ : ∀ (B : Type) [CommRing B] [Algebra S B] (x y : G₁.level v →ₐ[S] B),
      toConv (x.comp (θ : G₂.level w →ₐ[S] G₁.level v)) * toConv (y.comp (θ : G₂.level w →ₐ[S] G₁.level v)) =
        toConv ((toConv x * toConv y).ofConv.comp (θ : G₂.level w →ₐ[S] G₁.level v))) :
    G₂.level w ≃ₐc[S] G₁.level v :=
  BialgEquiv.ofAlgEquiv θ
    (by

      have hu := hθ S (1 : WithConv (G₁.level v →ₐ[S] S)).ofConv (1 : WithConv (G₁.level v →ₐ[S] S)).ofConv
      rw [toConv_ofConv, mul_one] at hu
      set U : WithConv (G₂.level w →ₐ[S] S) := toConv ((1 : WithConv (G₁.level v →ₐ[S] S)).ofConv.comp (θ : G₂.level w →ₐ[S] G₁.level v)) with hU
      have hP : (PDivisibleGroup.Point.ofConv U : G₂.Point S w) * PDivisibleGroup.Point.ofConv U = PDivisibleGroup.Point.ofConv U := by
        rw [← PDivisibleGroup.Point.ofConv_mul]; exact congrArg PDivisibleGroup.Point.ofConv hu
      have hP1 : (PDivisibleGroup.Point.ofConv U : G₂.Point S w) = 1 := mul_eq_left.1 hP
      have hU1 : U = 1 := congrArg PDivisibleGroup.Point.toConv hP1
      have key : (1 : WithConv (G₁.level v →ₐ[S] S)).ofConv.comp (θ : G₂.level w →ₐ[S] G₁.level v) = (1 : WithConv (G₂.level w →ₐ[S] S)).ofConv := by
        rw [← toConv_ofConv (1 : WithConv (G₂.level w →ₐ[S] S)), ← hU1]
      have e1 : (1 : WithConv (G₁.level v →ₐ[S] S)).ofConv = Bialgebra.counitAlgHom S (G₁.level v) := by
        rw [AlgHom.convOne_def, ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]
      have e2 : (1 : WithConv (G₂.level w →ₐ[S] S)).ofConv = Bialgebra.counitAlgHom S (G₂.level w) := by
        rw [AlgHom.convOne_def, ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]
      rw [← e1, ← e2]; exact key)
    (map_comp_comul_of_forall_convMul θ hθ)

@[scoped simp] theorem bialgEquivOfConvMul_apply (θ : G₂.level w ≃ₐ[S] G₁.level v) (hθ) (c : G₂.level w) :
    bialgEquivOfConvMul G₁ G₂ v w θ hθ c = θ c := rfl

end PointsBialg

end HBC
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

namespace HBC

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP WithConv

universe u

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem specMap_ofHom_inj {A B : Type u} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

theorem specMap_ofHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem map_comp_fst {W X Y Z S T : Scheme.{0}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ := pullback.lift_fst _ _ _

theorem map_comp_snd {W X Y Z S T : Scheme.{0}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ := pullback.lift_snd _ _ _

theorem isFinite_specMap_algebraMap (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)

theorem finpart_bc
    {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (φ : R →+* R') [IsLocalHom φ]
    {X U : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : U ⟶ X) [IsOpenImmersion j] [IsFinite (j ≫ f)]
    (hfib : ∀ x : X, f.base x = IsLocalRing.closedPoint R → x ∈ Set.range j.base) :
    let σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom φ)
    let j' : pullback (j ≫ f) σ ⟶ pullback f σ :=
      pullback.map (j ≫ f) σ f σ j (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    IsOpenImmersion j' ∧ IsFinite (pullback.snd (j ≫ f) σ) ∧
      ∀ x : ↥(pullback f σ), (pullback.snd f σ).base x = IsLocalRing.closedPoint R' → x ∈ Set.range j'.base := by
  intro σ j'
  let e := pullbackRightPullbackFstIso f σ j
  have hj' : j' = e.inv ≫ pullback.snd j (pullback.fst f σ) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ← pullback.condition, ← Category.assoc, pullbackRightPullbackFstIso_inv_fst]
    · rw [pullback.lift_snd, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd, Category.comp_id]
  have hej' : e.hom ≫ j' = pullback.snd j (pullback.fst f σ) := by
    rw [hj', Iso.hom_inv_id_assoc]
  refine ⟨?_, inferInstance, ?_⟩
  · rw [hj']; infer_instance
  · intro x hx
    haveI : IsLocalHom (CommRingCat.ofHom φ).hom := ‹IsLocalHom φ›
    have h1 : f.base ((pullback.fst f σ).base x) = IsLocalRing.closedPoint R := by
      change (pullback.fst f σ ≫ f).base x = _
      rw [pullback.condition]
      change σ.base ((pullback.snd f σ).base x) = _
      rw [hx]
      exact Spec_closedPoint
    have h2 : x ∈ ⇑(pullback.fst f σ) ⁻¹' Set.range ⇑j := hfib _ h1
    rw [← Scheme.Pullback.range_snd] at h2
    obtain ⟨y, hy⟩ := h2
    refine ⟨e.hom.base y, ?_⟩
    change (e.hom ≫ j') y = x
    rw [hej']
    exact hy

theorem range_subset_of_isFinite
    {R : Type} [CommRing R] [IsLocalRing R]
    {X T : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (s : T ⟶ X) [IsFinite (s ≫ f)]
    {U : Set X} (hU : IsOpen U) (hfib : ∀ x : X, f.base x = IsLocalRing.closedPoint R → x ∈ U) :
    Set.range s.base ⊆ U := by
  rintro _ ⟨t, rfl⟩
  have hc : IsClosed ((s ≫ f).base '' closure {t}) := (s ≫ f).isClosedMap _ isClosed_closure
  have hz : (s ≫ f).base t ∈ (s ≫ f).base '' closure {t} := ⟨t, subset_closure rfl, rfl⟩
  obtain ⟨t', ht', hft'⟩ := (IsLocalRing.specializes_closedPoint _).mem_closed hc hz
  exact ((specializes_iff_mem_closure.2 ht').map s.base.hom.continuous).mem_open hU (hfib _ hft')

theorem exists_iso_of_isFinite
    {R : Type} [CommRing R] [IsLocalRing R]
    {X U₁ U₂ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (j₁ : U₁ ⟶ X) (j₂ : U₂ ⟶ X) [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsFinite (j₁ ≫ f)] [IsFinite (j₂ ≫ f)]
    (h₁ : ∀ x : X, f.base x = IsLocalRing.closedPoint R → x ∈ Set.range j₁.base)
    (h₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R → x ∈ Set.range j₂.base) :
    ∃ e : U₁ ≅ U₂, e.hom ≫ j₂ = j₁ :=
  ⟨IsOpenImmersion.isoOfRangeEq j₁ j₂
    ((range_subset_of_isFinite f j₁ j₂.isOpenEmbedding.isOpen_range h₂).antisymm
      (range_subset_of_isFinite f j₂ j₁.isOpenEmbedding.isOpen_range h₁)),
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

section Datum

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rb : Type} [CommRing Rb] {h : ℕ} (𝒢b : PDivisibleGroup Rb p h)
  (ρb : XHDRLevel.R p →+* Rb) (ιb : ∀ v : ℕ, Spec (CommRingCat.of (𝒢b.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ιb v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rb (𝒢b.level v))) ≫ Spec.map (CommRingCat.ofHom ρb))
  (hιcl : ∀ (v : ℕ) (h1 : ιb v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rb (𝒢b.level v))) ≫ Spec.map (CommRingCat.ofHom ρb)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρb)) (ιb v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rb (𝒢b.level v)))) h1))

include hιbase hιcl in

theorem algHom_eq_of_specMap_comp_eq (v : ℕ) {B : Type} [CommRing B] [Algebra Rb B] (x y : 𝒢b.level v →ₐ[Rb] B)
    (hxy : Spec.map (CommRingCat.ofHom (x : 𝒢b.level v →+* B)) ≫ ιb v = Spec.map (CommRingCat.ofHom (y : 𝒢b.level v →+* B)) ≫ ιb v) :
    x = y := by
  haveI := hιcl v (hιbase v)
  have h2 : Spec.map (CommRingCat.ofHom (x : 𝒢b.level v →+* B)) ≫ pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρb)) (ιb v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rb (𝒢b.level v)))) (hιbase v) =
      Spec.map (CommRingCat.ofHom (y : 𝒢b.level v →+* B)) ≫ pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρb)) (ιb v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rb (𝒢b.level v)))) (hιbase v) := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using hxy
    · simp only [Category.assoc, pullback.lift_snd, specMap_ofHom_comp, AlgHom.comp_algebraMap]
  have h3 := specMap_ofHom_inj ((cancel_mono _).1 h2)
  exact AlgHom.ext fun a => DFunLike.congr_fun h3 a

end Datum
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

section Kernel

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)

noncomputable abbrev Kq (n : ℕ) : pullback (O.L.schemeNsmul n) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ⟶ base p :=
  pullback.fst (O.L.schemeNsmul n) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g

variable
  {Rh : Type} [CommRing Rh] [IsLocalRing Rh] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
  (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)
  {RD : Type} [CommRing RD] [IsLocalRing RD] [Algebra RD Rh] [IsLocalHom (algebraMap RD Rh)]
  (𝒢D : PDivisibleGroup RD p h)
  (ρD : XHDRLevel.R p →+* RD) (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
  (hρ : (algebraMap RD Rh).comp ρD = ρh)
  (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
  (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
  (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint RD →
          x ∈ Set.range jv.base)

include hιbase hιp hιfin hρ hιDbase hιDp hιDfin in

theorem exists_iso_level (v : ℕ) :
    ∃ Θ : Spec (CommRingCat.of (𝒢.level v)) ≅ Spec (CommRingCat.of (Rh ⊗[RD] 𝒢D.level v)),
      Θ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Rh (Rh ⊗[RD] 𝒢D.level v))) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ∧
      Θ.hom ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : 𝒢D.level v →ₐ[RD] Rh ⊗[RD] 𝒢D.level v) :
          𝒢D.level v →+* Rh ⊗[RD] 𝒢D.level v)) ≫ ιD v = ι v := by

  let q : pullback (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ⟶ base p := Kq O (p ^ v)
  let σh : Spec (CommRingCat.of Rh) ⟶ base p := Spec.map (CommRingCat.ofHom ρh)
  let σD : Spec (CommRingCat.of RD) ⟶ base p := Spec.map (CommRingCat.ofHom ρD)
  let σφ : Spec (CommRingCat.of Rh) ⟶ Spec (CommRingCat.of RD) := Spec.map (CommRingCat.ofHom (algebraMap RD Rh))
  have hσ : σφ ≫ σD = σh := by simp only [σφ, σD, σh, specMap_ofHom_comp, hρ]

  have h4h : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
        (ι v) (ι v ≫ O.g) (hιp v) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ σh := by
    rw [← Category.assoc, pullback.lift_fst]; exact hιbase v
  have h4D : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
        (ιD v) (ιD v ≫ O.g) (hιDp v) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ σD := by
    rw [← Category.assoc, pullback.lift_fst]; exact hιDbase v
  obtain ⟨hoh, -, hfibh⟩ := hιfin v (hιp v) h4h
  obtain ⟨hoD, -, hfibD⟩ := hιDfin v (hιDp v) h4D

  obtain ⟨jh, hoh', hfibh', jh_snd, jh_fst_fst⟩ :
      ∃ jh : Spec (CommRingCat.of (𝒢.level v)) ⟶ pullback q σh, IsOpenImmersion jh ∧
        (∀ x : ↥(pullback q σh), (pullback.snd q σh).base x = IsLocalRing.closedPoint Rh → x ∈ Set.range jh.base) ∧
        jh ≫ pullback.snd q σh = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ∧
        jh ≫ pullback.fst q σh ≫ pullback.fst _ _ = ι v :=
    ⟨_, hoh, hfibh, pullback.lift_snd _ _ _, by rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]⟩
  obtain ⟨jD, hoD', hfibD', jD_snd, jD_fst_fst⟩ :
      ∃ jD : Spec (CommRingCat.of (𝒢D.level v)) ⟶ pullback q σD, IsOpenImmersion jD ∧
        (∀ x : ↥(pullback q σD), (pullback.snd q σD).base x = IsLocalRing.closedPoint RD → x ∈ Set.range jD.base) ∧
        jD ≫ pullback.snd q σD = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ∧
        jD ≫ pullback.fst q σD ≫ pullback.fst _ _ = ιD v :=
    ⟨_, hoD, hfibD, pullback.lift_snd _ _ _, by rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]⟩
  clear hoh hfibh hoD hfibD h4h h4D
  haveI := hoh'
  haveI := hoD'

  haveI : IsFinite (jD ≫ (pullback.snd q σD)) := by rw [jD_snd]; exact isFinite_specMap_algebraMap RD (𝒢D.level v)
  obtain ⟨hoj', hfin', hfib'⟩ := finpart_bc (algebraMap RD Rh) (pullback.snd q σD) jD (fun x hx => hfibD' x hx)
  set j' := pullback.map (jD ≫ (pullback.snd q σD)) σφ (pullback.snd q σD) σφ jD (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    with hj'
  have j'_snd : j' ≫ pullback.snd (pullback.snd q σD) σφ = pullback.snd (jD ≫ (pullback.snd q σD)) σφ := by rw [hj', map_comp_snd, Category.comp_id]
  have j'_fst : j' ≫ pullback.fst (pullback.snd q σD) σφ = pullback.fst (jD ≫ (pullback.snd q σD)) σφ ≫ jD := by rw [hj', map_comp_fst]
  haveI := hoj'
  haveI : IsFinite (j' ≫ pullback.snd (pullback.snd q σD) σφ) := by rw [j'_snd]; exact hfin'

  let e1 := pullbackLeftPullbackSndIso q σD σφ
  let e2 : pullback q (σφ ≫ σD) ≅ pullback q σh := pullback.congrHom rfl hσ
  let e := e1 ≪≫ e2
  have e_inv_snd : e.inv ≫ pullback.snd (pullback.snd q σD) σφ = pullback.snd q σh := by
    simp only [e, Iso.trans_inv, Category.assoc, e1, pullbackLeftPullbackSndIso_inv_snd_snd, e2, pullback.congrHom_inv,
      map_comp_snd, Category.comp_id]
  have e_inv_fst_fst : e.inv ≫ pullback.fst (pullback.snd q σD) σφ ≫ pullback.fst q σD = pullback.fst q σh := by
    simp only [e, Iso.trans_inv, Category.assoc, e1, pullbackLeftPullbackSndIso_inv_fst, e2, pullback.congrHom_inv,
      map_comp_fst, Category.comp_id]
  have e_hom_snd : e.hom ≫ pullback.snd q σh = pullback.snd (pullback.snd q σD) σφ := by
    rw [← e_inv_snd, Iso.hom_inv_id_assoc]
  let jh' : Spec (CommRingCat.of (𝒢.level v)) ⟶ pullback (pullback.snd q σD) σφ := jh ≫ e.inv
  have jh'_snd : jh' ≫ pullback.snd (pullback.snd q σD) σφ = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) := by
    rw [Category.assoc, e_inv_snd, jh_snd]
  have jh'_fst_fst_fst : jh' ≫ pullback.fst (pullback.snd q σD) σφ ≫ pullback.fst q σD ≫ pullback.fst _ _ = ι v := by
    rw [Category.assoc, reassoc_of% e_inv_fst_fst]
    exact jh_fst_fst
  haveI : IsOpenImmersion jh' := inferInstance
  haveI : IsFinite (jh' ≫ pullback.snd (pullback.snd q σD) σφ) := by rw [jh'_snd]; exact isFinite_specMap_algebraMap Rh (𝒢.level v)
  have hfibh'' : ∀ x : ↥(pullback (pullback.snd q σD) σφ), (pullback.snd (pullback.snd q σD) σφ).base x = IsLocalRing.closedPoint Rh → x ∈ Set.range jh'.base := by
    intro x hx
    have hx' : (pullback.snd q σh).base (e.hom.base x) = IsLocalRing.closedPoint Rh := by
      change (e.hom ≫ pullback.snd q σh).base x = _
      rw [e_hom_snd]; exact hx
    obtain ⟨y, hy⟩ := hfibh' _ hx'
    refine ⟨y, ?_⟩
    change e.inv.base (jh.base y) = x
    rw [hy]
    change (e.hom ≫ e.inv).base x = x
    rw [e.hom_inv_id]; rfl

  obtain ⟨ε, hε⟩ := exists_iso_of_isFinite (pullback.snd (pullback.snd q σD) σφ) jh' j' hfibh'' hfib'

  let e3 : pullback (jD ≫ (pullback.snd q σD)) σφ ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) σφ := pullback.congrHom jD_snd rfl
  have e3_hom_snd : e3.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [e3, pullback.congrHom_hom, map_comp_snd, Category.comp_id]
  have e3_hom_fst : e3.hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp only [e3, pullback.congrHom_hom, map_comp_fst, Category.comp_id]
  let e4 := pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) σφ
  let e5 := pullbackSpecIso RD Rh (𝒢D.level v)
  refine ⟨ε ≪≫ e3 ≪≫ e4 ≪≫ e5, ?_, ?_⟩
  ·
    simp only [Iso.trans_hom, Category.assoc]
    rw [pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst, e3_hom_snd, ← j'_snd, reassoc_of% hε, jh'_snd]
  ·
    simp only [Iso.trans_hom, Category.assoc]
    rw [pullbackSpecIso_hom_snd_assoc, pullbackSymmetry_hom_comp_snd_assoc, reassoc_of% e3_hom_fst, ← jD_fst_fst,
      ← reassoc_of% j'_fst, reassoc_of% hε, jh'_fst_fst_fst]

end Kernel
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

end HBC
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

namespace HBC

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP WithConv

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem exists_algEquiv_of_iso {S A C : Type} [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (Θ : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of C))
    (hΘ : Θ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) = Spec.map (CommRingCat.ofHom (algebraMap S A))) :
    ∃ θ : C ≃ₐ[S] A, Spec.map (CommRingCat.ofHom (θ : C →+* A)) = Θ.hom := by
  let ψ : CommRingCat.of C ⟶ CommRingCat.of A := Spec.preimage Θ.hom
  let ψ' : CommRingCat.of A ⟶ CommRingCat.of C := Spec.preimage Θ.inv
  have hψ : Spec.map ψ = Θ.hom := Spec.map_preimage _
  have hψ' : Spec.map ψ' = Θ.inv := Spec.map_preimage _
  have h1 : ψ ≫ ψ' = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hψ, hψ', Iso.inv_hom_id, Spec.map_id])
  have h2 : ψ' ≫ ψ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hψ, hψ', Iso.hom_inv_id, Spec.map_id])
  let I : CommRingCat.of C ≅ CommRingCat.of A := ⟨ψ, ψ', h1, h2⟩
  let r : C ≃+* A := I.commRingCatIsoToRingEquiv
  have hcomm : ∀ s : S, r (algebraMap S C s) = algebraMap S A s := by
    intro s
    have h3 : CommRingCat.ofHom (algebraMap S C) ≫ ψ = CommRingCat.ofHom (algebraMap S A) :=
      Spec.map_injective (by rw [Spec.map_comp, hψ]; exact hΘ)
    exact congr($(congrArg CommRingCat.Hom.hom h3) s)
  refine ⟨AlgEquiv.ofRingEquiv (f := r) hcomm, ?_⟩
  rw [← hψ]
  rfl

section Mult

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  {RD : Type} [CommRing RD] [Algebra RD Rh]
  (𝒢D : PDivisibleGroup RD p h)
  (ρD : XHDRLevel.R p →+* RD) (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
  (hρ : (algebraMap RD Rh).comp ρD = ρh)
  (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
  (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) h1))
  (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra RD B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (v : ℕ) (θ : (Rh ⊗[RD] 𝒢D.level v) ≃ₐ[Rh] 𝒢.level v)
  (hKL : Spec.map (CommRingCat.ofHom (θ : Rh ⊗[RD] 𝒢D.level v →+* 𝒢.level v)) ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : 𝒢D.level v →ₐ[RD] Rh ⊗[RD] 𝒢D.level v) :
        𝒢D.level v →+* Rh ⊗[RD] 𝒢D.level v)) ≫ ιD v = ι v)

theorem mul_coe_congr {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst e
  rw [Subtype.ext hx, Subtype.ext hy]

include hKL in

theorem spec_restr_comp_ιD {B : Type} [CommRing B] [Algebra RD B] [Algebra Rh B] [IsScalarTower RD Rh B]
    (z : 𝒢.level v →ₐ[Rh] B) :
    Spec.map (CommRingCat.ofHom ((restr (z.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) : 𝒢D.level v →+* B))) ≫ ιD v =
      Spec.map (CommRingCat.ofHom (z : 𝒢.level v →+* B)) ≫ ι v := by
  have hr : ((restr (z.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) : 𝒢D.level v →+* B)) =
      (z : 𝒢.level v →+* B).comp ((θ : Rh ⊗[RD] 𝒢D.level v →+* 𝒢.level v).comp
        ((Algebra.TensorProduct.includeRight : 𝒢D.level v →ₐ[RD] Rh ⊗[RD] 𝒢D.level v) : 𝒢D.level v →+* Rh ⊗[RD] 𝒢D.level v)) :=
    RingHom.ext fun _ => rfl
  rw [hr, ← specMap_ofHom_comp, ← specMap_ofHom_comp, Category.assoc, Category.assoc, hKL]

include hιbase hιmul hρ hιDbase hιDcl hιDmul hKL in

theorem convMul_comp (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.level v →ₐ[Rh] B) :
    toConv (x.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) * toConv (y.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) =
      toConv ((toConv x * toConv y).ofConv.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) := by
  letI : Algebra RD B := ((algebraMap Rh B).comp (algebraMap RD Rh)).toAlgebra
  haveI : IsScalarTower RD Rh B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply WithConv.ofConv_injective
  apply eq_of_restr_eq (R := RD)
  rw [restr_convMul, ofConv_toConv]

  apply algHom_eq_of_specMap_comp_eq O 𝒢D ρD ιD hιDbase hιDcl v

  have ht : Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD) =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [specMap_ofHom_comp, specMap_ofHom_comp, ← hρ, ← RingHom.comp_assoc]

  have hxh : (Spec.map (CommRingCat.ofHom (x : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [Category.assoc, hιbase, ← Category.assoc, specMap_ofHom_comp, AlgHom.comp_algebraMap]
  have hyh : (Spec.map (CommRingCat.ofHom (y : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [Category.assoc, hιbase, ← Category.assoc, specMap_ofHom_comp, AlgHom.comp_algebraMap]
  have hxD : (Spec.map (CommRingCat.ofHom ((restr (x.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) : 𝒢D.level v →+* B))) ≫ ιD v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD) := by
    rw [Category.assoc, hιDbase, ← Category.assoc, specMap_ofHom_comp, AlgHom.comp_algebraMap]
  have hyD : (Spec.map (CommRingCat.ofHom ((restr (y.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)) : 𝒢D.level v →+* B))) ≫ ιD v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD) := by
    rw [Category.assoc, hιDbase, ← Category.assoc, specMap_ofHom_comp, AlgHom.comp_algebraMap]

  have hD := hιDmul v B (Point.ofAlgHom (restr (x.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v))))
    (Point.ofAlgHom (restr (y.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)))) hxD hyD

  have hh := hιmul v B (Point.ofAlgHom x) (Point.ofAlgHom y) hxh hyh
  change Spec.map (CommRingCat.ofHom ((Point.toAlgHom (Point.ofAlgHom (restr (x.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v))) *
      Point.ofAlgHom (restr (y.comp (θ : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v)))) : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v = _
  rw [hD, spec_restr_comp_ιD O 𝒢 ι 𝒢D ιD v θ hKL]
  change _ = Spec.map (CommRingCat.ofHom ((Point.toAlgHom (Point.ofAlgHom x * Point.ofAlgHom y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v
  rw [hh]
  exact mul_coe_congr O.L ht _ _ _ _ (spec_restr_comp_ιD O 𝒢 ι 𝒢D ιD v θ hKL x) (spec_restr_comp_ιD O 𝒢 ι 𝒢D ιD v θ hKL y)

end Mult
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

end HBC
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

namespace HBC

open PDivisibleGroup ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP WithConv

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem comp_eq_of_faithfulSMul {Rp Rh RD L : Type} [CommRing Rp] [CommRing Rh] [CommRing RD] [CommRing L]
    [Algebra Rh L] [FaithfulSMul Rh L] [Algebra RD Rh] [Algebra RD L] [IsScalarTower RD Rh L]
    (ρh : Rp →+* Rh) (ρD : Rp →+* RD) (f : Rp →+* L)
    (hρh : (algebraMap Rh L).comp ρh = f) (hρD : (algebraMap RD L).comp ρD = f) :
    (algebraMap RD Rh).comp ρD = ρh := by
  refine RingHom.ext fun r => FaithfulSMul.algebraMap_injective Rh L ?_
  change algebraMap Rh L (algebraMap RD Rh (ρD r)) = algebraMap Rh L (ρh r)
  rw [← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply, hρD, ← hρh, RingHom.comp_apply]

theorem isLocalHom_algebraMap_decompRing (Pl : ValuationSubring ℚ̄) (Rh : Type) [CommRing Rh] [IsLocalRing Rh] [Algebra Rh ℚ̄]
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh ℚ̄ x) < 1)
    [Algebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh]
    [IsScalarTower ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh ℚ̄] :
    IsLocalHom (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh) := by
  refine ⟨fun a ha => ?_⟩
  have hnm : algebraMap _ Rh a ∉ maximalIdeal Rh := fun hm => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hm)) ha
  have hnlt : ¬ Pl.valuation (a : ℚ̄) < 1 := by
    intro hlt
    apply hnm
    rw [hRloc, ← IsScalarTower.algebraMap_apply]
    exact hlt
  have haPl : (a : ℚ̄) ∈ Pl := (Subring.mem_inf.1 a.2).1
  have haK : (a : ℚ̄) ∈ IntermediateField.fixedField (Pl.decompositionSubgroup ℚ) := (Subring.mem_inf.1 a.2).2
  have hv1 : Pl.valuation (a : ℚ̄) = 1 := ((Pl.valuation_le_one_iff _).2 haPl).eq_of_not_lt hnlt
  have ha0 : (a : ℚ̄) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hinvPl : (a : ℚ̄)⁻¹ ∈ Pl := (Pl.valuation_le_one_iff _).1 (by rw [map_inv₀, hv1, inv_one])
  have hinvK : (a : ℚ̄)⁻¹ ∈ IntermediateField.fixedField (Pl.decompositionSubgroup ℚ) := inv_mem haK
  have hinv : (a : ℚ̄)⁻¹ ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring :=
    Subring.mem_inf.2 ⟨hinvPl, hinvK⟩
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

section Core

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {Pl : ValuationSubring ℚ̄} {hPl : Pl.LiesOverPrime p}
  [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM Pl}
  (O : JHNeronObjectAtP p M H hpM Pl hPl Λ)
  {Rh : Type} [CommRing Rh] [IsLocalRing Rh] [Nontrivial Rh] [Algebra Rh ℚ̄] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
  (ρh : XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
  (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
  (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
  (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
  (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
  (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)
  (Δ : 𝒢.Points ℚ̄ →+ JH M H)
  (hιpts : ∀ (v : ℕ) (x : 𝒢.Point ℚ̄ v),
      (O.pts (Δ (𝒢.pointsMkAdd ℚ̄ v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] ℚ̄) : 𝒢.level v →+* ℚ̄)) ≫ ι v)
  {RD : Type} [CommRing RD] [IsLocalRing RD] [Algebra RD Rh] [IsLocalHom (algebraMap RD Rh)] [Algebra RD ℚ̄] [IsScalarTower RD Rh ℚ̄]
  (𝒢D : PDivisibleGroup RD p h)
  (ρD : XHDRLevel.R p →+* RD) (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
  (hρ : (algebraMap RD Rh).comp ρD = ρh)
  (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
  (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) h1))
  (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
  (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra RD B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[RD] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap RD B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
  (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
  (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap RD (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint RD →
          x ∈ Set.range jv.base)
  (ΔD : 𝒢D.Points ℚ̄ →+ JH M H)
  (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point ℚ̄ v),
      (O.pts (ΔD (𝒢D.pointsMkAdd ℚ̄ v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[RD] ℚ̄) : 𝒢D.level v →+* ℚ̄)) ≫ ιD v)

include hιbase hιcl hιp hιmul hιt hιfin hιpts hρ hιDbase hιDcl hιDp hιDmul hιDt hιDfin hιDpts in
theorem core :
    ∃ e : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] (𝒢D.baseChange Rh).level v,
      (∀ v : ℕ, ((𝒢D.baseChange Rh).transition v).comp (e (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] (𝒢D.baseChange Rh).level (v + 1)) =
        (e v : 𝒢.level v →ₐc[Rh] (𝒢D.baseChange Rh).level v).comp (𝒢.transition v)) ∧
      (∀ (v : ℕ) (x : 𝒢.Point ℚ̄ v), ∃ y : 𝒢D.Point ℚ̄ v,
        (∀ b : 𝒢D.level v, PDivisibleGroup.Point.toAlgHom y b =
          PDivisibleGroup.Point.toAlgHom x ((e v).symm ((1 : Rh) ⊗ₜ[RD] b))) ∧
        Δ (𝒢.pointsMkAdd ℚ̄ v (Additive.ofMul x)) = ΔD (𝒢D.pointsMkAdd ℚ̄ v (Additive.ofMul y))) := by
  choose Θ hΘover hΘKL using fun v => exists_iso_level O 𝒢 ρh ι hιbase hιp hιfin 𝒢D ρD ιD hρ hιDbase hιDp hιDfin v
  choose θ hθ using fun v => exists_algEquiv_of_iso (S := Rh) (Θ v) (hΘover v)
  have hKL : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (θ v : Rh ⊗[RD] 𝒢D.level v →+* 𝒢.level v)) ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : 𝒢D.level v →ₐ[RD] Rh ⊗[RD] 𝒢D.level v) :
        𝒢D.level v →+* Rh ⊗[RD] 𝒢D.level v)) ≫ ιD v = ι v := fun v => by
    rw [hθ]; exact hΘKL v
  have MULT := fun v => convMul_comp O 𝒢 ρh ι hιbase hιmul 𝒢D ρD ιD hρ hιDbase hιDcl hιDmul v (θ v) (hKL v)
  let e : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] (𝒢D.baseChange Rh).level v := fun v =>
    (bialgEquivOfConvMul 𝒢 (𝒢D.baseChange Rh) v v (θ v) (MULT v)).symm

  have hKL' : ∀ w : ℕ, Spec.map (CommRingCat.ofHom ((θ w).symm : 𝒢.level w →+* Rh ⊗[RD] 𝒢D.level w)) ≫ ι w =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : 𝒢D.level w →ₐ[RD] Rh ⊗[RD] 𝒢D.level w) :
        𝒢D.level w →+* Rh ⊗[RD] 𝒢D.level w)) ≫ ιD w := fun w => by
    have hid : ((θ w).symm : 𝒢.level w →+* Rh ⊗[RD] 𝒢D.level w).comp (θ w : Rh ⊗[RD] 𝒢D.level w →+* 𝒢.level w) = RingHom.id _ :=
      RingHom.ext fun a => (θ w).symm_apply_apply a
    rw [← hKL w, ← Category.assoc, specMap_ofHom_comp, hid, CommRingCat.ofHom_id]
    erw [Spec.map_id]
    exact (Category.id_comp _).symm
  refine ⟨e, fun v => ?_, fun v x => ?_⟩
  ·
    apply BialgHom.coe_algHom_injective
    apply algHom_eq_of_specMap_comp_eq O 𝒢 ρh ι hιbase hιcl (v + 1)

    have hT : ((Bialgebra.TensorProduct.map (BialgHom.id Rh Rh) (𝒢D.transition v) :
          Rh ⊗[RD] 𝒢D.level (v + 1) →ₐc[Rh] Rh ⊗[RD] 𝒢D.level v) : Rh ⊗[RD] 𝒢D.level (v + 1) →+* Rh ⊗[RD] 𝒢D.level v).comp
        ((Algebra.TensorProduct.includeRight : 𝒢D.level (v + 1) →ₐ[RD] Rh ⊗[RD] 𝒢D.level (v + 1)) :
          𝒢D.level (v + 1) →+* Rh ⊗[RD] 𝒢D.level (v + 1)) =
        ((Algebra.TensorProduct.includeRight : 𝒢D.level v →ₐ[RD] Rh ⊗[RD] 𝒢D.level v) : 𝒢D.level v →+* Rh ⊗[RD] 𝒢D.level v).comp
          (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v) := RingHom.ext fun _ => rfl
    have key : Spec.map (CommRingCat.ofHom (((Bialgebra.TensorProduct.map (BialgHom.id Rh Rh) (𝒢D.transition v) :
          Rh ⊗[RD] 𝒢D.level (v + 1) →ₐc[Rh] Rh ⊗[RD] 𝒢D.level v) : Rh ⊗[RD] 𝒢D.level (v + 1) →+* Rh ⊗[RD] 𝒢D.level v).comp
            ((θ (v + 1)).symm : 𝒢.level (v + 1) →+* Rh ⊗[RD] 𝒢D.level (v + 1)))) ≫ ι (v + 1) =
        Spec.map (CommRingCat.ofHom (((θ v).symm : 𝒢.level v →+* Rh ⊗[RD] 𝒢D.level v).comp
          (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v))) ≫ ι (v + 1) := by
      rw [← specMap_ofHom_comp, ← specMap_ofHom_comp, Category.assoc, Category.assoc, hKL' (v + 1), hιt v, hKL' v,
        ← Category.assoc, specMap_ofHom_comp, hT, ← specMap_ofHom_comp, Category.assoc, hιDt v]
    exact key
  ·
    refine ⟨Point.ofAlgHom (restr ((Point.toAlgHom x).comp (θ v : Rh ⊗[RD] 𝒢D.level v →ₐ[Rh] 𝒢.level v))), fun b => rfl, ?_⟩
    apply O.pts.injective
    apply Subtype.ext
    rw [hιpts, hιDpts]
    exact (spec_restr_comp_ιD O 𝒢 ι 𝒢D ιD v (θ v) (hKL v) (Point.toAlgHom x)).symm

end Core
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

end HBC
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP.HBC"

set_option linter.unusedVariables false in
open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)

    [Algebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh]
    [IsScalarTower ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh (AlgebraicClosure ℚ)]

    [IsDiscreteValuationRing ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)]

    (𝒢D : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p h)
    (ΔD : 𝒢D.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔDinj : Function.Injective ΔD)
    (hΔDlev : ∀ (v : ℕ) (x : ModularCurve.JH M H),
      (∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = x) ↔ x ∈ O.finPts (p ^ v))
    (hΔDgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢D.Points (AlgebraicClosure ℚ), ΔD (τ' • z) = τ • ΔD z)
    (htorD : ∀ v : ℕ, O.toricPts (p ^ v) ≤ O.finPts (p ^ v))

    (ρD : ModularCurve.XHDRLevel.R p →+* (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)))
    (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
    (hρD : (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (AlgebraicClosure ℚ)).comp ρD = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
    (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h1))
    (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
    (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) →
          x ∈ Set.range jv.base)

    (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (O.pts (ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] (AlgebraicClosure ℚ)) : 𝒢D.level v →+* (AlgebraicClosure ℚ))) ≫ ιD v)
    :
    ∃ e : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] (𝒢D.baseChange Rh).level v,

      (∀ v : ℕ, ((𝒢D.baseChange Rh).transition v).comp (e (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] (𝒢D.baseChange Rh).level (v + 1)) =
        (e v : 𝒢.level v →ₐc[Rh] (𝒢D.baseChange Rh).level v).comp (𝒢.transition v)) ∧

      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v), ∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v,
        (∀ b : 𝒢D.level v, PDivisibleGroup.Point.toAlgHom y b =
          PDivisibleGroup.Point.toAlgHom x ((e v).symm ((1 : Rh) ⊗ₜ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] b))) ∧
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))) := by
  haveI : IsLocalHom (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh) :=
    HBC.isLocalHom_algebraMap_decompRing Pl Rh hRloc
  have hρ : (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) Rh).comp ρD = ρh :=
    HBC.comp_eq_of_faithfulSMul ρh ρD _ hρh hρD
  exact HBC.core O 𝒢 ρh ι hιbase hιcl hιp hιmul hιt hιfin Δ hιpts 𝒢D ρD ιD hρ hιDbase hιDcl hιDp hιDmul hιDt hιDfin ΔD hιDpts

end S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP
end P2MW
export P2MW.S_ModularCurve_exists_bialgEquiv_baseChange_decompositionRing_finitePart_jHNeronObjectAtP (solution)
