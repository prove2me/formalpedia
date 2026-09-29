-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/68cbe252-1825-552b-a076-9be0ba902ad6

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_obstruction_two_cocycle_of_local_lifts
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (L₀ : RelativeGroupLaw T f₀) (h₀ : AbelianSchemePropertyBundle T f₀)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (hck : Lk.IsCommutative) (hAk : AbelianSchemePropertyBundle (ResidueField T') fk)
    (hLk : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i₀ =
        (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨P.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, Q.2]⟩).1)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)

    (𝒲 : (pullback fk fk).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤
      (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ
        (𝒰.comap i₀).U (lam₃ w)) :
    letI := algebraOfHom fk Ue
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).cochain 𝒲 1,
        (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).d 𝒲 1 b =
          OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk)
              (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1
              𝒲 (𝒰.comap i₀) lam₃ h₃ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.fst fk fk)
              𝒲 (𝒰.comap i₀) lam₁ h₁ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.snd fk fk)
              𝒲 (𝒰.comap i₀) lam₂ h₂ 2 (ω.1 a ξ) := by
  classical
  letI instUe := algebraOfHom fk Ue

  obtain ⟨ιW, UW, hUWa, hUWs⟩ := 𝒲

  have N0 := GoodReductionJacobian.RelativeGroupLaw.exists_product_local_lifts_of_local_lifts
      T' T π hπ hker f₀ L₀ ρ hρ 𝒰 Y q hq g hg fk Lk i₀ hi₀ hLk (Scheme.OrderedAffineCover.mk ιW UW hUWa hUWs)
      lam₁ lam₂ lam₃ h₁ h₂ h₃
  dsimp only at N0
  obtain ⟨instjP, hjP, Vop, hVaff, hVcov, hVW, hV₁, hV₂, hV₃, Z, qZ, instZ, hqZ, gZ, hgZ, hZ₁, hZ₂, hZ₃, hhZ₁, hhZ₂, hhZ₃⟩ := N0

  generalize hjPdef : ((pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
      (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) : pullback fk fk ⟶ pullback f₀ f₀) = jP at instjP hjP hVW

  obtain rfl : UW = fun w => jP ⁻¹ᵁ (Vop w) := funext fun w => (hVW w).symm
  haveI := instjP
  haveI := instZ

  let 𝒱 : (pullback f₀ f₀).OrderedAffineCover :=
    { ι := ιW, U := Vop, isAffineOpen := hVaff, iSup_eq_top := hVcov }

  haveI : IsSeparated (pullback.fst f₀ f₀ ≫ f₀) := inferInstance
  haveI : Smooth (pullback.fst f₀ f₀ ≫ f₀) := inferInstance
  haveI : IsSeparated (pullback.fst fk fk ≫ fk) := inferInstance

  show ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).cochain (𝒱.comap jP) 1,
        (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).d (𝒱.comap jP) 1 b =
          OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1
              (𝒱.comap jP) (𝒰.comap i₀) lam₃ h₃ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.fst fk fk)
              (𝒱.comap jP) (𝒰.comap i₀) lam₁ h₁ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.snd fk fk)
              (𝒱.comap jP) (𝒰.comap i₀) lam₂ h₂ 2 (ω.1 a ξ)
  intro a ξ

  obtain ⟨LP, hLP₁, hLP₂, hLPe, hLPμ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_pullback_fst_snd_mul_hom fk Lk
  have hLPμ' := @hLPμ hck

  have hone_fst : (LP.one (𝟙 _)).1 ≫ pullback.fst fk fk = (Lk.one (𝟙 _)).1 := (hLPe (𝟙 _)).1
  have hone_snd : (LP.one (𝟙 _)).1 ≫ pullback.snd fk fk = (Lk.one (𝟙 _)).1 := (hLPe (𝟙 _)).2
  have hone_mu : (LP.one (𝟙 _)).1 ≫ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 = (Lk.one (𝟙 _)).1 := by
    have hnat := Lk.mul_natural (pullback.fst fk fk ≫ fk) (𝟙 _) (LP.one (𝟙 _)).1
      (by rw [(LP.one (𝟙 _)).2]) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩
    have h1 : schemeHomOverComp (LP.one (𝟙 _)).1 (by rw [(LP.one (𝟙 _)).2]) ⟨pullback.fst fk fk, rfl⟩ = Lk.one (𝟙 _) :=
      Subtype.ext (by rw [schemeHomOverComp_coe]; exact hone_fst)
    have h2 : schemeHomOverComp (LP.one (𝟙 _)).1 (by rw [(LP.one (𝟙 _)).2])
        (⟨pullback.snd fk fk, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst fk fk ≫ fk) fk) = Lk.one (𝟙 _) :=
      Subtype.ext (by rw [schemeHomOverComp_coe]; exact hone_snd)
    have := congrArg Subtype.val hnat
    rw [schemeHomOverComp_coe, h1, h2, Lk.one_mul] at this
    exact this

  obtain ⟨U', hU', e'₁, he'₁, hU'₁, hU'₂, hU'₃⟩ : ∃ (U' : (pullback fk fk).Opens) (_ : IsAffineOpen U')
      (e'₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (U' : Scheme.{u})) (_ : e'₁ ≫ U'.ι = (LP.one (𝟙 _)).1),
      U' ≤ pullback.fst fk fk ⁻¹ᵁ Ue ∧ U' ≤ pullback.snd fk fk ⁻¹ᵁ Ue ∧ U' ≤ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue := by
    let pt : ↥(Spec (CommRingCat.of (ResidueField T'))) := ⟨⊥, Ideal.isPrime_bot⟩
    let W₀ : (pullback fk fk).Opens :=
      pullback.fst fk fk ⁻¹ᵁ Ue ⊓ pullback.snd fk fk ⁻¹ᵁ Ue ⊓ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue
    have hmemUe : ∀ (x : Spec (CommRingCat.of (ResidueField T')) ⟶ pullback fk fk) (h : pullback fk fk ⟶ Ak)
        (hx : x ≫ h = (Lk.one (𝟙 _)).1), (x ≫ h).base pt ∈ (Ue : Set Ak) := by
      intro x h hx
      rw [hx, ← he₁, ← Scheme.Opens.range_ι Ue]
      exact ⟨e₁.base pt, rfl⟩
    have hW : (LP.one (𝟙 _)).1.base pt ∈ W₀ := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show ((LP.one (𝟙 _)).1 ≫ pullback.fst fk fk).base pt ∈ (Ue : Set Ak); exact hmemUe _ _ hone_fst
      · show ((LP.one (𝟙 _)).1 ≫ pullback.snd fk fk).base pt ∈ (Ue : Set Ak); exact hmemUe _ _ hone_snd
      · show ((LP.one (𝟙 _)).1 ≫ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1).base pt ∈ (Ue : Set Ak); exact hmemUe _ _ hone_mu
    obtain ⟨U'', hU'aff, hmem, hle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens (pullback fk fk))) hW
    let U' : (pullback fk fk).Opens := U''
    have hrange : Set.range (LP.one (𝟙 _)).1.base ⊆ Set.range U'.ι.base := by
      rintro _ ⟨y, rfl⟩
      have : y = pt := Subsingleton.elim _ _
      rw [this, Scheme.Opens.range_ι]
      exact hmem
    exact ⟨U', hU'aff, IsOpenImmersion.lift U'.ι (LP.one (𝟙 _)).1 hrange, IsOpenImmersion.lift_fac _ _ _,
      hle.trans (inf_le_left.trans inf_le_left), hle.trans (inf_le_left.trans inf_le_right), hle.trans inf_le_right⟩

  obtain ⟨OP, hOP, hOPm, hOPtop, hOPinf, hOPaff, σP, hσP₁, hσP₂, φP, hφPq, hφPg, hφPO, ρPab, ρPbc, ρPac, hρPab, hρPbc, hρPac,
      ωP, hωP, hωPZ⟩ :=
    AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts
      T' T π hπ hker hsmall (pullback.fst f₀ f₀ ≫ f₀) hI ρ hρ V ι hι hιI 𝒱 Z qZ hqZ gZ hgZ
      (pullback.fst fk fk ≫ fk) LP jP hjP U' hU' e'₁ he'₁

  obtain ⟨b₁, hb₁⟩ :=
    AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
      T' T π hπ hker hsmall hI ρ hρ V ι hι hιI
      f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ
      (pullback.fst f₀ f₀ ≫ f₀) 𝒱 Z qZ hqZ gZ hgZ (pullback.fst fk fk ≫ fk) LP jP hjP U' hU' e'₁ he'₁
      OP hOP hOPm hOPtop hOPinf hOPaff σP hσP₁ hσP₂ φP hφPq hφPg hφPO ρPab ρPbc ρPac hρPab hρPbc hρPac ωP hωP hωPZ
      (pullback.fst f₀ f₀) rfl lam₁ hV₁ (pullback.fst fk fk) (by rw [← hjPdef, pullback.lift_fst]) rfl
      (fun t P Q => hLP₁ t P Q) hU'₁ h₁ hZ₁ (fun w => (hhZ₁ w).1) (fun w => (hhZ₁ w).2) a ξ

  obtain ⟨b₂, hb₂⟩ :=
    AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
      T' T π hπ hker hsmall hI ρ hρ V ι hι hιI
      f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ
      (pullback.fst f₀ f₀ ≫ f₀) 𝒱 Z qZ hqZ gZ hgZ (pullback.fst fk fk ≫ fk) LP jP hjP U' hU' e'₁ he'₁
      OP hOP hOPm hOPtop hOPinf hOPaff σP hσP₁ hσP₂ φP hφPq hφPg hφPO ρPab ρPbc ρPac hρPab hρPbc hρPac ωP hωP hωPZ
      (pullback.snd f₀ f₀) pullback.condition.symm lam₂ hV₂ (pullback.snd fk fk) (by rw [← hjPdef, pullback.lift_snd])
      pullback.condition.symm (fun t P Q => hLP₂ t P Q) hU'₂ h₂ hZ₂ (fun w => (hhZ₂ w).1) (fun w => (hhZ₂ w).2) a ξ

  have hhk₃ : (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ≫ i₀ = jP ≫ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 := by
    have hψ : jP ≫ (pullback.fst f₀ f₀ ≫ f₀) =
        (pullback.fst fk fk ≫ fk) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [← hjPdef, ← Category.assoc, pullback.lift_fst, Category.assoc, hi₀.w, Category.assoc]
    have hnat := L₀.mul_natural (pullback.fst f₀ f₀ ≫ f₀) ((pullback.fst fk fk ≫ fk) ≫ Spec.map (CommRingCat.ofHom ρ))
      jP hψ ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩
    have e1 : schemeHomOverComp jP hψ
        (⟨pullback.fst f₀ f₀, rfl⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) =
        ⟨pullback.fst fk fk ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, (⟨pullback.fst fk fk, rfl⟩ : SchemeHomOver (pullback.fst fk fk ≫ fk) fk).2]⟩ :=
      Subtype.ext (by rw [schemeHomOverComp_coe, ← hjPdef, pullback.lift_fst])
    have e2 : schemeHomOverComp jP hψ
        (⟨pullback.snd f₀ f₀, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f₀ f₀ ≫ f₀) f₀) =
        ⟨pullback.snd fk fk ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, (⟨pullback.snd fk fk, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst fk fk ≫ fk) fk).2]⟩ :=
      Subtype.ext (by rw [schemeHomOverComp_coe, ← hjPdef, pullback.lift_snd])
    have := congrArg Subtype.val hnat
    rw [schemeHomOverComp_coe, e1, e2] at this
    rw [this]
    exact hLk _ _ _
  obtain ⟨b₃, hb₃⟩ :=
    AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
      T' T π hπ hker hsmall hI ρ hρ V ι hι hιI
      f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ
      (pullback.fst f₀ f₀ ≫ f₀) 𝒱 Z qZ hqZ gZ hgZ (pullback.fst fk fk ≫ fk) LP jP hjP U' hU' e'₁ he'₁
      OP hOP hOPm hOPtop hOPinf hOPaff σP hσP₁ hσP₂ φP hφPq hφPg hφPO ρPab ρPbc ρPac hρPab hρPbc hρPac ωP hωP hωPZ
      (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).2 lam₃ hV₃ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 hhk₃ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).2
      (fun t P Q => hLPμ' t P Q) hU'₃ h₃ hZ₃ (fun w => (hhZ₃ w).1) (fun w => (hhZ₃ w).2) a ξ

  have hN3 := GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
    (ResidueField T') fk Lk Ue hUe U' hU' hU'₁ hU'₂ hU'₃ e'₁
    (by rw [← Category.assoc, he'₁]; exact hone_fst) (by rw [← Category.assoc, he'₁]; exact hone_snd) _ ωP a
  have hN3ξ := congrArg (fun φ : Module.Dual (ResidueField T') V →ₗ[ResidueField T'] _ => φ ξ) hN3
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at hN3ξ

  refine ⟨b₃ - b₁ - b₂, ?_⟩
  rw [map_sub, map_sub, ← hb₁, ← hb₂, ← hb₃]
  rw [sub_sub, sub_eq_zero] at hN3ξ
  rw [hN3ξ]
  abel

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle (solution)
