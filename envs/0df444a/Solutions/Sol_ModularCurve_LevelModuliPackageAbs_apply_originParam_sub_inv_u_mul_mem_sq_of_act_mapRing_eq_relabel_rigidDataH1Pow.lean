-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d12c1ca7-072f-54b8-a593-2c6bb747bfb4

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
import Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
import Theorems.Thm_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
import Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] SubalgebraClass.toAlgebra
attribute [local instance 10001] AdicCompletion.instAlgebra

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LinCoreAux

open MvPowerSeries Filter Topology

variable {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
  {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A]

theorem hasEval_of_mem {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) :
    letI : WithIdeal A := ⟨I⟩; MvPowerSeries.HasEval a := by
  letI : WithIdeal A := ⟨I⟩
  refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), ?_⟩
  rw [Filter.cofinite_eq_bot]; exact tendsto_bot

theorem eval₂_sub_lin_mem_sq (f : MvPowerSeries Unit R₀) (hf : MvPowerSeries.constantCoeff f = 0) (t : A) (ht : t ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) (fun _ : Unit => t) f) -
      algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single () 1) f) * t ∈ I ^ 2 := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have ha : ∀ s : Unit, (fun _ : Unit => t) s ∈ I := fun _ => ht
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I (fun _ : Unit => t) ha) f
  have hopen : IsOpen ((Submodule.toAddSubgroup (I ^ 2) : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨2, trivial, by simp⟩
  have hclosed : IsClosed ((I ^ 2 : Ideal A) : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  have hclosed' : IsClosed {z : A | z - algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single () 1) f) * t ∈ I ^ 2} :=
    hclosed.preimage (continuous_id.sub continuous_const)
  refine hclosed'.mem_of_tendsto hsum (Filter.eventually_atTop.mpr ⟨{Finsupp.single () 1}, ?_⟩)
  intro s hs
  have hmem1 : Finsupp.single () 1 ∈ s := hs (by simp)
  show (∑ d ∈ s, _) - _ ∈ I ^ 2
  rw [← Finset.add_sum_erase s _ hmem1]
  have hprod : ∀ d : Unit →₀ ℕ, (d.prod fun s e => (fun _ : Unit => t) s ^ e) = t ^ (d ()) := by
    intro d; rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_subsingleton _ ()]
  have t1 : algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single () 1) f) *
      ((Finsupp.single () 1).prod fun s e => (fun _ : Unit => t) s ^ e) =
      algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single () 1) f) * t := by
    rw [hprod]; simp
  rw [t1, show ∀ S y : A, y + S - y = S from fun S y => by ring]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [Finset.mem_erase] at hd
  obtain ⟨hd1, -⟩ := hd
  by_cases hz : d = 0
  · subst hz; rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hf, map_zero, zero_mul]; exact Submodule.zero_mem _
  refine Ideal.mul_mem_left _ _ ?_
  rw [hprod]
  have hdeg : 2 ≤ d () := by
    by_contra hlt
    push_neg at hlt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hlt) with e0 | e0
    · exact hz (by ext i; simp [e0])
    · exact hd1 (by ext i; simp [e0])
  exact Ideal.pow_le_pow_right hdeg (Ideal.pow_mem_pow ht _)

end LinCoreAux

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hℓA : IsUnit ((ℓg : ℕ) : A₀))
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

    [IsDomain R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)

    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)

    (hssJ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ιΩ : k →+* Ω),
      ιΩ (resR (ι P₀.j₀)) ∈ ModularCurve.ssJSet q Ω)

    (χP χQ : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hBC : F.IsBaseChange resR F₀)
    (hDr : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (hmax : maximalIdeal R = Ideal.span {originParam χP, originParam χQ})
    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁)

    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (ργ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hpin : ∀ (T : Type) [Field T] [DecidableEq T] [Algebra A₀ T]
        (y y' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y'.level.2.1.xP y'.level.2.1.yP =
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
            ModularCurve.LevelRelabelling.toPoint ((y.curve).baseChange T) y.level.2.1.xP y.level.2.1.yP →
        y'.level.2.1.xQ = y'.level.2.1.xP → y'.level.2.1.yQ = y'.level.2.1.yP →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) y.level.2.2 hΔ →
        ργ.act (Quot.mk _ y) = Quot.mk _ y')
    (hfix : ∀ b : P₀.B₀, ι (P₀.classify (ργ.act P₀.univ) b) - ι b ∈ maximalIdeal R)

    (θ₀ : R →ₐ[W₀] R)
    (hcompl : ∀ b : P₀.B₀, θ₀ (ι b) = ι (P₀.classify (ργ.act P₀.univ) b))
    (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)

    (V : WeierstrassCurve.VariableChange R)
    (hΔ : IsUnit ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.Δ)
    (x' : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw R)
    (hact : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act V ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x)) = x')
    (hcurve : x'.curve = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve)
    (hlev1 : x'.level.1 = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1)
    (hlev22 : x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ)
    [DecidableEq (FractionRing R)]

    (hlev21 : ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
        (algebraMap R (FractionRing R) x'.level.2.1.xP) (algebraMap R (FractionRing R) x'.level.2.1.yP) =
      (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) •
        ModularCurve.LevelRelabelling.toPoint ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve).baseChange (FractionRing R))
          (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.xP) (algebraMap R (FractionRing R) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1.yP))
    (hlev21' : x'.level.2.1.xQ = x'.level.2.1.xP ∧ x'.level.2.1.yQ = x'.level.2.1.yP) :
    (θ₀ (originParam χP) - ((V.u⁻¹ : Rˣ) : R) * (((γ 0 0 : ℤ) : R) * originParam χP + ((γ 1 0 : ℤ) : R) * originParam χQ) ∈
        (maximalIdeal R) ^ 2) ∧
    (θ₀ (originParam χQ) - ((V.u⁻¹ : Rˣ) : R) * (((γ 0 1 : ℤ) : R) * originParam χP + ((γ 1 1 : ℤ) : R) * originParam χQ) ∈
        (maximalIdeal R) ^ 2) := by
  classical

  have hθA : ∀ r : R, (θ₀.restrictScalars A₀) r = θ₀ r := fun r => rfl

  have hEQ : 𝒯.act V (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2) =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ := by
    rw [← hlev22, ← hact]
    rfl

  obtain ⟨hc₁, hpin₁⟩ := h𝒯.2 R R (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2
  obtain ⟨φ₁, hφ₁, hco₁⟩ := hCO R R (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve
  obtain ⟨hP₁, hQ₁⟩ := hpin₁ φ₁ hφ₁ hco₁
  have auxMap : ∀ (W' : WeierstrassCurve R) (hW' : W' = ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve.map (θ₀.restrictScalars A₀).toRingHom)
      (P' : Section W') (P₀ : Section ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve) (χ : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R),
      ReducesToOrigin P₀ χ (maximalIdeal R) →
      P'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ₁ hφ₁ =
        Spec.map (CommRingCat.ofHom (θ₀.restrictScalars A₀).toRingHom) ≫ P₀.1 →
      ∃ χ' : OriginChartRing W' →+* R, ReducesToOrigin P' χ' ((maximalIdeal R).map (θ₀.restrictScalars A₀).toRingHom) ∧
        originParam χ' = θ₀ (originParam χ) := by
    intro W' hW' P' P₀ χ hχ h
    subst hW'
    simp only [eqToHom_refl, Category.id_comp] at h
    obtain ⟨χ', h1, h2, -⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
        ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve (θ₀.restrictScalars A₀).toRingHom φ₁ hφ₁ hco₁ P₀ χ (maximalIdeal R) hχ P' h
    exact ⟨χ', h1, h2⟩
  obtain ⟨χP₁, hχP₁, hzP₁⟩ := auxMap _ hc₁ _ _ χP hP hP₁
  obtain ⟨χQ₁, hχQ₁, hzQ₁⟩ := auxMap _ hc₁ _ _ χQ hQ hQ₁

  have hmaple : (maximalIdeal R).map (θ₀.restrictScalars A₀).toRingHom ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap]
    have h := hres r
    have : (θ₀.restrictScalars A₀).toRingHom r = (θ₀ r - r) + r := by rw [sub_add_cancel]; rfl
    rw [this]
    exact Ideal.add_mem _ h hr
  have hred : ∀ {W' : WeierstrassCurve R} (P' : Section W') (χ : OriginChartRing W' →+* R),
      ReducesToOrigin P' χ ((maximalIdeal R).map (θ₀.restrictScalars A₀).toRingHom) → ReducesToOrigin P' χ (maximalIdeal R) :=
    fun P' χ h => ⟨h.1, hmaple h.2.1, hmaple h.2.2⟩
  replace hχP₁ := hred _ _ hχP₁
  replace hχQ₁ := hred _ _ hχQ₁

  have gen : ∀ z : RawDrinfeldPair R, z = 𝒯.act V (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2) →
      ∃ hc : z.curve = V • (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve,
        ∀ (φ : projModelGradingCR (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+*ᵍ
            projModelGradingCR (V • (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V • (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)).map φ),
          IsVariableChangeHom (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve V φ →
            z.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).P.1 ∧
            z.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).Q.1 := by
    intro z hz; subst hz
    exact h𝒯.1 R V (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2)

  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  let g' : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j % (q : ℤ)).toNat : ℕ) : ℤ)
  have hg'val : ∀ i j, g' i j = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j % (q : ℤ) := fun i j => Int.toNat_of_nonneg (Int.emod_nonneg _ hq0)
  have hgg' : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod q)) = g'.map (Int.castRingHom (ZMod q)) := by
    ext i j
    simp only [Matrix.map_apply, Int.coe_castRingHom, hg'val, ZMod.intCast_mod]
  have hlev : RawDrinfeldPair.IsLevel 𝒢 q ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).curve ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 :=
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).isLevel.1.2.2
  have hrel : ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ :=
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
      𝒢 q (Fact.out : q.Prime).two_le R _ _ hΔ hlev _ _ hgg'
  obtain ⟨hc₂, hpin₂⟩ := gen _ (hEQ.trans hrel).symm
  obtain ⟨φ₂, hφ₂, hvc₂⟩ := hVC R (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve V
  obtain ⟨hP₂, hQ₂⟩ := hpin₂ φ₂ hφ₂ hvc₂
  have auxAct : ∀ (W' : WeierstrassCurve R)
      (hW' : W' = V • (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)
      (P' : Section W') (P₀ : Section (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve)
      (χ : OriginChartRing (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve →+* R),
      ReducesToOrigin P₀ χ (maximalIdeal R) →
      P'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ₂ hφ₂ = P₀.1 →
      ∃ χ' : OriginChartRing W' →+* R, ReducesToOrigin P' χ' (maximalIdeal R) ∧
        originParam χ' = (letI : WithIdeal R := ⟨maximalIdeal R⟩;
          FormalGroup.evalSeries ((𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.variableChangeSeries V)
            (originParam χ)) := by
    intro W' hW' P' P₀ χ hχ h
    subst hW'
    simp only [eqToHom_refl, Category.id_comp] at h
    exact WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
      _ V φ₂ hφ₂ hvc₂ P₀ χ hχ P' h
  obtain ⟨χP₂, hχP₂, hzP₂⟩ := auxAct _ hc₂ _ _ χP₁ hχP₁ hP₂
  obtain ⟨χQ₂, hχQ₂, hzQ₂⟩ := auxAct _ hc₂ _ _ χQ₁ hχQ₁ hQ₂
  rw [hzP₁] at hzP₂
  rw [hzQ₁] at hzQ₂

  haveI hEll : (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).IsElliptic := ⟨hΔ⟩
  set a₀ : ℕ := ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 % (q : ℤ)).toNat) with ha₀
  set b₀ : ℕ := ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 % (q : ℤ)).toNat) with hb₀
  set a₁ : ℕ := ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 % (q : ℤ)).toNat) with ha₁
  set b₁ : ℕ := ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 % (q : ℤ)).toNat) with hb₁
  obtain ⟨χ₃, hχ₃, hz₃⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve F hFW (𝒢 R _ hΔ) (h𝒢 R _ hΔ) (h𝒢O R _ hΔ)
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χP χQ hP hQ a₀ b₀
  obtain ⟨χ₄, hχ₄, hz₄⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve F hFW (𝒢 R _ hΔ) (h𝒢 R _ hΔ) (h𝒢O R _ hΔ)
    ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χP χQ hP hQ a₁ b₁

  have hPeq : (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ).P =
      linComb (𝒢 R _ hΔ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q a₀ b₀ := rfl
  have hQeq : (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2 hΔ).Q =
      linComb (𝒢 R _ hΔ) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q a₁ b₁ := rfl

  have huniq : ∀ (S : Section ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve) (c d : OriginChartRing ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve →+* R),
      IsOriginChartSection S c → IsOriginChartSection S d → c = d := by
    intro S c d hc hd
    unfold IsOriginChartSection at hc hd
    have h1 : Spec.map (CommRingCat.ofHom c) = Spec.map (CommRingCat.ofHom d) := by
      rw [← cancel_mono (originChartι ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve), ← hc, ← hd]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have eP : χP₂ = χ₃ := huniq _ χP₂ χ₃ (hPeq ▸ hχP₂.1) hχ₃.1
  have eQ : χQ₂ = χ₄ := huniq _ χQ₂ χ₄ (hQeq ▸ hχQ₂.1) hχ₄.1

  rw [eP] at hzP₂
  rw [eQ] at hzQ₂
  have EP : (letI : WithIdeal R := ⟨maximalIdeal R⟩;
      FormalGroup.evalSeries ((𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.variableChangeSeries V)
        (θ₀ (originParam χP))) =
      F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₀ b₀ := hzP₂.symm.trans hz₃
  have EQ : (letI : WithIdeal R := ⟨maximalIdeal R⟩;
      FormalGroup.evalSeries ((𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve.variableChangeSeries V)
        (θ₀ (originParam χQ))) =
      F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₁ b₁ := hzQ₂.symm.trans hz₄
  clear hzP₂ hzQ₂

  have hθm : ∀ r : R, r ∈ maximalIdeal R → θ₀ r ∈ maximalIdeal R := fun r hr => hmaple (Ideal.mem_map_of_mem _ hr)
  have hx₀m : originParam χP ∈ maximalIdeal R := hP.2.1
  have hx₁m : originParam χQ ∈ maximalIdeal R := hQ.2.1
  set Wy := (𝒯.map (θ₀.restrictScalars A₀) ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2).curve with hWy
  have hψ0 : MvPowerSeries.constantCoeff (Wy.variableChangeSeries V) = 0 := WeierstrassCurve.constantCoeff_variableChangeSeries Wy V
  have hψ1 : MvPowerSeries.coeff (Finsupp.single () 1) (Wy.variableChangeSeries V) = ((V.u : Rˣ) : R) :=
    WeierstrassCurve.coeff_one_variableChangeSeries Wy V
  have A1P := @LinCoreAux.eval₂_sub_lin_mem_sq R _ ⊥ inferInstance R _ _ (maximalIdeal R) _ (Wy.variableChangeSeries V) hψ0 _ (hθm _ hx₀m)
  have A1Q := @LinCoreAux.eval₂_sub_lin_mem_sq R _ ⊥ inferInstance R _ _ (maximalIdeal R) _ (Wy.variableChangeSeries V) hψ0 _ (hθm _ hx₁m)
  rw [hψ1, Algebra.algebraMap_self, RingHom.id_apply] at A1P A1Q

  replace A1P : (letI : WithIdeal R := ⟨maximalIdeal R⟩; FormalGroup.evalSeries (Wy.variableChangeSeries V) (θ₀ (originParam χP))) -
      ((V.u : Rˣ) : R) * θ₀ (originParam χP) ∈ maximalIdeal R ^ 2 := A1P
  replace A1Q : (letI : WithIdeal R := ⟨maximalIdeal R⟩; FormalGroup.evalSeries (Wy.variableChangeSeries V) (θ₀ (originParam χQ))) -
      ((V.u : Rˣ) : R) * θ₀ (originParam χQ) ∈ maximalIdeal R ^ 2 := A1Q
  rw [EP] at A1P
  rw [EQ] at A1Q

  obtain ⟨-, A3P, -⟩ := FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
    R (maximalIdeal R) F (originParam χP) (originParam χQ) hx₀m hx₁m a₀ b₀
  obtain ⟨-, A3Q, -⟩ := FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
    R (maximalIdeal R) F (originParam χP) (originParam χQ) hx₀m hx₁m a₁ b₁
  have hqm : ((q : ℕ) : R) ∈ maximalIdeal R := by
    rw [← hkerR, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hcast : ∀ (z : ℤ), (((z % (q : ℤ)).toNat : ℕ) : R) - (z : R) ∈ maximalIdeal R := by
    intro z
    have h1 : (((z % (q : ℤ)).toNat : ℕ) : ℤ) = z % (q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0)
    have h2 : (((z % (q : ℤ)).toNat : ℕ) : R) = ((z % (q : ℤ) : ℤ) : R) := by rw [← Int.cast_natCast, h1]
    rw [h2, ← Int.cast_sub, show z % (q : ℤ) - z = -((q : ℤ) * (z / (q : ℤ))) by linear_combination Int.emod_add_mul_ediv z q,
      Int.cast_neg, Int.cast_mul, Int.cast_natCast]
    exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hqm)
  have A4P : ((a₀ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : R)) * originParam χP + ((b₀ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : R)) * originParam χQ ∈
      maximalIdeal R ^ 2 := by
    rw [pow_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul (hcast _) hx₀m) (Ideal.mul_mem_mul (hcast _) hx₁m)
  have A4Q : ((a₁ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : R)) * originParam χP + ((b₁ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : R)) * originParam χQ ∈
      maximalIdeal R ^ 2 := by
    rw [pow_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul (hcast _) hx₀m) (Ideal.mul_mem_mul (hcast _) hx₁m)
  have key : ((V.u⁻¹ : Rˣ) : R) * ((V.u : Rˣ) : R) = 1 := Units.inv_mul _
  refine ⟨?_, ?_⟩
  · have e : θ₀ (originParam χP) - ((V.u⁻¹ : Rˣ) : R) * (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : R) * originParam χP + ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : R) * originParam χQ) =
        ((V.u⁻¹ : Rˣ) : R) * (-(F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₀ b₀ - ((V.u : Rˣ) : R) * θ₀ (originParam χP)) +
          (F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₀ b₀ - ((a₀ : R) * originParam χP + (b₀ : R) * originParam χQ)) +
          (((a₀ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : R)) * originParam χP + ((b₀ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : R)) * originParam χQ)) := by
      linear_combination (-(θ₀ (originParam χP))) * key
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ A1P) A3P) A4P)
  · have e : θ₀ (originParam χQ) - ((V.u⁻¹ : Rˣ) : R) * (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : R) * originParam χP + ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : R) * originParam χQ) =
        ((V.u⁻¹ : Rˣ) : R) * (-(F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₁ b₁ - ((V.u : Rˣ) : R) * θ₀ (originParam χQ)) +
          (F.linCombAdic (maximalIdeal R) (originParam χP) (originParam χQ) a₁ b₁ - ((a₁ : R) * originParam χP + (b₁ : R) * originParam χQ)) +
          (((a₁ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : R)) * originParam χP + ((b₁ : R) - ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : R)) * originParam χQ)) := by
      linear_combination (-(θ₀ (originParam χQ))) * key
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.add_mem _ (Submodule.neg_mem _ A1Q) A3Q) A4Q)

end S_ModularCurve_LevelModuliPackageAbs_apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_apply_originParam_sub_inv_u_mul_mem_sq_of_act_mapRing_eq_relabel_rigidDataH1Pow (solution)
