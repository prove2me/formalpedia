-- Prove2me | solution 1 for ModularCurve.XOneP.natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_toric_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4e237b37-e4be-556d-9174-c7118d0d253c

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_toric_of_curveModel_igusa_twoChartModel_x1_mul

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace DispBoundX1

theorem card_le_of_generator {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (I : Subgroup G) (J : AddSubgroup V) (T : Set V) (n : ℕ)
    (hT : ∀ σ ∈ I, ∀ y ∈ T, σ • y = y)
    (hdisp : ∀ σ ∈ I, ∀ x ∈ J, σ • x - x ∈ T)
    (hstab : ∀ σ ∈ I, ∀ x ∈ J, σ • x ∈ J)
    (htors : ∀ x ∈ J, n • x = 0)
    (γ : G) (hγ : γ ∈ I)
    (hgen : ∀ τ ∈ I, ∃ (j : ℕ) (y w : G), y ∈ I ∧ w ∈ I ∧ τ = γ ^ j * y ^ n * w ^ n) :
    Nat.card ↥J ≤
      Nat.card ↥((fun x : V => γ • x - x) '' (J : Set V)) * Nat.card ↥{x : V | x ∈ J ∧ ∀ σ ∈ I, σ • x = x} := by
  classical

  have hmul : ∀ x ∈ J, ∀ σ ∈ I, ∀ τ ∈ I, (σ * τ) • x - x = (σ • x - x) + (τ • x - x) := by
    intro x hx σ hσ τ hτ
    have h1 : σ • (τ • x - x) = τ • x - x := hT σ hσ _ (hdisp τ hτ x hx)
    rw [smul_sub] at h1
    rw [mul_smul]
    calc σ • τ • x - x = (σ • τ • x - σ • x) + (σ • x - x) := by abel
      _ = (τ • x - x) + (σ • x - x) := by rw [h1]
      _ = (σ • x - x) + (τ • x - x) := add_comm _ _
  have hpow : ∀ x ∈ J, ∀ σ ∈ I, ∀ j : ℕ, σ ^ j • x - x = j • (σ • x - x) := by
    intro x hx σ hσ j
    induction j with
    | zero => rw [pow_zero, one_smul, sub_self, zero_nsmul]
    | succ j ih => rw [pow_succ, hmul x hx _ (I.pow_mem hσ j) σ hσ, ih, add_nsmul, one_nsmul]
  have hkill : ∀ x ∈ J, ∀ σ ∈ I, σ ^ n • x - x = 0 := by
    intro x hx σ hσ
    rw [hpow x hx σ hσ n]
    exact htors _ (J.sub_mem (hstab σ hσ x hx) hx)

  have hker : ∀ x ∈ J, γ • x = x → ∀ τ ∈ I, τ • x = x := by
    intro x hx hγx τ hτ
    obtain ⟨j, y, w, hy, hw, hτeq⟩ := hgen τ hτ
    have hIγ : γ ^ j ∈ I := I.pow_mem hγ j
    have hIy : y ^ n ∈ I := I.pow_mem hy n
    have hIw : w ^ n ∈ I := I.pow_mem hw n
    have e1 : τ • x - x = 0 := by
      rw [hτeq, hmul x hx _ (I.mul_mem hIγ hIy) _ hIw, hmul x hx _ hIγ _ hIy,
        hkill x hx y hy, hkill x hx w hw, hpow x hx γ hγ j, hγx, sub_self, nsmul_zero, add_zero, add_zero]
    exact sub_eq_zero.mp e1

  obtain ⟨f, hf⟩ : ∃ f : ↥J →+ V, ∀ x, f x = γ • (x : V) - x :=
    ⟨AddMonoidHom.mk' (fun x => γ • (x : V) - x) (fun x y => by
      show γ • ((x + y : ↥J) : V) - (x + y : ↥J) = (γ • (x : V) - x) + (γ • (y : V) - y)
      rw [AddSubgroup.coe_add, smul_add]
      exact (sub_add_sub_comm _ _ _ _).symm), fun _ => rfl⟩

  by_cases hfin : Finite ↥J
  swap
  · calc Nat.card ↥J = 0 := @Nat.card_eq_zero_of_infinite _ (not_finite_iff_infinite.mp hfin)
      _ ≤ _ := Nat.zero_le _

  have e1 : Nat.card ↥J = Nat.card (↥J ⧸ f.ker) * Nat.card ↥f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have e2 : Nat.card (↥J ⧸ f.ker) = Nat.card ↥f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

  set S : Set V := (fun x : V => γ • x - x) '' (J : Set V) with hSdef
  have hrangeS : ∀ y ∈ f.range, y ∈ S := by
    intro y hy
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, x.2, (hf x).symm.trans hx⟩
  have hSJ : ∀ y ∈ S, y ∈ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact J.sub_mem (hstab γ hγ x hx) hx
  haveI hSfin : Finite ↥S :=
    Finite.of_injective (fun s : ↥S => (⟨s.1, hSJ s.1 s.2⟩ : ↥J)) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h)
  set Fx : Set V := {x : V | x ∈ J ∧ ∀ σ ∈ I, σ • x = x} with hFxdef
  haveI hHfin : Finite ↥Fx :=
    Finite.of_injective (fun s : ↥Fx => (⟨s.1, s.2.1⟩ : ↥J)) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h)
  have h1 : Nat.card ↥f.range ≤ Nat.card ↥S :=
    Nat.card_le_card_of_injective (fun y : ↥f.range => (⟨y.1, hrangeS y.1 y.2⟩ : ↥S)) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h)

  have hkermem : ∀ x : ↥J, x ∈ f.ker → (x : V) ∈ Fx := by
    intro x hx
    rw [AddMonoidHom.mem_ker, hf, sub_eq_zero] at hx
    exact ⟨x.2, hker x x.2 hx⟩
  have h2 : Nat.card ↥f.ker ≤ Nat.card ↥Fx := by
    refine Nat.card_le_card_of_injective (fun x => (⟨((x : ↥J) : V), hkermem x x.2⟩ : ↥Fx)) ?_
    intro a b h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have h12 : Nat.card ↥f.range * Nat.card ↥f.ker ≤ Nat.card ↥S * Nat.card ↥Fx := Nat.mul_le_mul h1 h2
  calc Nat.card ↥J = Nat.card (↥J ⧸ f.ker) * Nat.card ↥f.ker := e1
    _ = Nat.card ↥f.range * Nat.card ↥f.ker := congrArg (fun t => t * Nat.card ↥f.ker) e2
    _ ≤ _ := h12

end DispBoundX1

namespace DispBoundX1

theorem main {Q : Type u} [Field Q] [Algebra ℚ Q] (L : Type v) [Field L] [Algebra L Q]
    {V : Type w} [AddCommGroup V] [DistribMulAction (Q ≃ₐ[ℚ] Q) V]
    (I₀ : Subgroup (Q ≃ₐ[ℚ] Q)) (J : AddSubgroup V) (n : ℕ)
    (hmemJ : ∀ x : V, x ∈ J ↔ ((n : ℕ) : ℤ) • x = 0)
    (toric : V → Prop)
    (γ : Q ≃ₐ[ℚ] Q) (hγI : γ ∈ I₀) (hγL : ∀ l : L, γ (algebraMap L Q l) = algebraMap L Q l)
    (hγ : ∀ τ : Q ≃ₐ[ℚ] Q, τ ∈ I₀ → (∀ l : L, τ (algebraMap L Q l) = algebraMap L Q l) →
      ∃ (j : ℕ) (x w : Q ≃ₐ[ℚ] Q),
        x ∈ I₀ ∧ (∀ l : L, x (algebraMap L Q l) = algebraMap L Q l) ∧
        w ∈ I₀ ∧ (∀ l : L, w (algebraMap L Q l) = algebraMap L Q l) ∧
        τ = γ ^ j * x ^ n * w ^ n)
    (hdisp : ∀ σ : Q ≃ₐ[ℚ] Q, σ ∈ I₀ → (∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l) →
      ∀ x ∈ J, toric (σ • x - x))
    (hfix : ∀ σ : Q ≃ₐ[ℚ] Q, σ ∈ I₀ → (∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l) →
      ∀ x ∈ J, toric x → σ • x = x) :
    Nat.card ↥J ≤
      Nat.card ↥((fun x : V => γ • x - x) '' (J : Set V)) *
        Nat.card ↥{x : V | x ∈ J ∧ ∀ σ : Q ≃ₐ[ℚ] Q, σ ∈ I₀ →
          (∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l) → σ • x = x} := by

  let IL : Subgroup (Q ≃ₐ[ℚ] Q) :=
    { carrier := {σ | σ ∈ I₀ ∧ ∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l}
      mul_mem' := fun {σ τ} hσ hτ => ⟨I₀.mul_mem hσ.1 hτ.1, fun l => by
        rw [AlgEquiv.mul_apply, hτ.2 l, hσ.2 l]⟩
      one_mem' := ⟨I₀.one_mem, fun l => rfl⟩
      inv_mem' := fun {σ} hσ => ⟨I₀.inv_mem hσ.1, fun l => by
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
        exact (hσ.2 l).symm⟩ }
  have hIL : ∀ σ : Q ≃ₐ[ℚ] Q, σ ∈ IL ↔ (σ ∈ I₀ ∧ ∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l) :=
    fun σ => Iff.rfl

  have hstab : ∀ σ ∈ IL, ∀ x ∈ J, σ • x ∈ J := by
    intro σ _ x hx
    rw [hmemJ] at hx ⊢
    rw [smul_comm ((n : ℕ) : ℤ) σ x, hx, smul_zero]
  have htors : ∀ x ∈ J, n • x = 0 := by
    intro x hx
    rw [← natCast_zsmul]
    exact (hmemJ x).mp hx

  let T : Set V := {v | v ∈ J ∧ toric v}
  have hT : ∀ σ ∈ IL, ∀ v ∈ T, σ • v = v := fun σ hσ v hv => hfix σ hσ.1 hσ.2 v hv.1 hv.2
  have hdispT : ∀ σ ∈ IL, ∀ x ∈ J, σ • x - x ∈ T := fun σ hσ x hx =>
    ⟨J.sub_mem (hstab σ hσ x hx) hx, hdisp σ hσ.1 hσ.2 x hx⟩
  have hgen : ∀ τ ∈ IL, ∃ (j : ℕ) (y w : Q ≃ₐ[ℚ] Q), y ∈ IL ∧ w ∈ IL ∧ τ = γ ^ j * y ^ n * w ^ n := by
    intro τ hτ
    obtain ⟨j, x, w, hxI, hxL, hwI, hwL, h⟩ := hγ τ hτ.1 hτ.2
    exact ⟨j, x, w, ⟨hxI, hxL⟩, ⟨hwI, hwL⟩, h⟩
  have key := DispBoundX1.card_le_of_generator IL J T n hT hdispT hstab htors γ ⟨hγI, hγL⟩ hgen
  have hFx : {x : V | x ∈ J ∧ ∀ σ ∈ IL, σ • x = x} =
      {x : V | x ∈ J ∧ ∀ σ : Q ≃ₐ[ℚ] Q, σ ∈ I₀ →
        (∀ l : L, σ (algebraMap L Q l) = algebraMap L Q l) → σ • x = x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact and_congr_right' ⟨fun h σ h1 h2 => h σ ((hIL σ).2 ⟨h1, h2⟩),
      fun h σ hσ => h σ ((hIL σ).1 hσ).1 ((hIL σ).1 hσ).2⟩
  rw [hFx] at key
  exact key

end DispBoundX1

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)
    (ℓ k' : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hγI : γ ∈ Pl.inertiaSubgroupIn ℚ)
    (hγL : ∀ l : L, γ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l)
    (hγ : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ Pl.inertiaSubgroupIn ℚ → (∀ l : L, τ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        x ∈ Pl.inertiaSubgroupIn ℚ ∧ (∀ l : L, x (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
        w ∈ Pl.inertiaSubgroupIn ℚ ∧ (∀ l : L, w (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
        τ = γ ^ j * x ^ (ℓ ^ k') * w ^ (ℓ ^ k'))
    (hdisp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Pl.inertiaSubgroupIn ℚ → (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k'),
        ∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s), (gpts (σ • x - x)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 ∧ (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Pl.inertiaSubgroupIn ℚ → (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k'), ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
        (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → G.proj y = 0 → σ • x = x) :
    Nat.card ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k')) ≤
      Nat.card ↥((fun x : ModularCurve.JOne (M * p) => γ • x - x) ''
          (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k') : Set (ModularCurve.JOne (M * p)))) *
        Nat.card ↥{x : ModularCurve.JOne (M * p) | x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k') ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Pl.inertiaSubgroupIn ℚ →
            (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) → σ • x = x} :=
  DispBoundX1.main (Q := AlgebraicClosure ℚ) L (Pl.inertiaSubgroupIn ℚ)
    (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (ℓ ^ k')) (ℓ ^ k')
    (fun _ => Pic0.mem_torsion)
    (fun v : ModularCurve.JOne (M * p) =>
      ∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
        (gpts v).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 ∧
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0)
    γ hγI hγL hγ hdisp
    (fun σ hσI hσL x hx ⟨z, y, h1, h2, h3⟩ => hfix σ hσI hσL x hx z y h1 h2 h3)

#print axioms solution

end S_ModularCurve_XOneP_natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_toric_of_curveModel_igusa_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_natCard_torsion_le_natCard_image_smul_sub_mul_natCard_inertiaInvariants_of_forall_smul_sub_toric_of_curveModel_igusa_twoChartModel_x1_mul (solution)
