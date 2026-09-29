-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a5e7b625-65c2-5738-b16f-e9223f545aa6

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

set_option maxHeartbeats 4000000 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)

    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (p : HeightOneSpectrum (𝓞 ℚ))

    (hsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, F.whittakerLoc p (g * k) = F.whittakerLoc p g)
    (hirr : ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc p), W ≠ 0 → F.whittakerLoc p ∈ gl3CyclicSubspace W)
    (hadm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ Bs : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (Bs : Set (LocalGL3 p → ℂ)))
    (hne : F.whittakerLoc p ≠ 0)

    (ωp : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcent : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      F.whittakerLoc p (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωp t : ℂˣ) : ℂ) * F.whittakerLoc p h)
    (d : ℕ)
    (hKd : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 p, F.whittakerLoc p (g * k) = F.whittakerLoc p g)

    (c₀ : ℕ)
    (hν : ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar ν w) c)

    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)
    (hB : c₀ + 6 ≤ B) (hBd : 2 * d + 1 ≤ B)
    (hωu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((ωp z : ℂˣ) : ℂ)‖ = 1)

    (hFg : IsGaugeMajorised3 ℚ F.whittaker)
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ S' → ¬ IsBadPlace K ν q)

    (Δ : ℕ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (hE1 : E = 1) (hEd1 : Ed = 1) (hε : ε ≠ 0) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 3 * B + Δ)
    (hωℓ : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(ℓ : ℤ)) → (ωp * ξ ^ 3) u = 1)
    (h31 : ∀ g : LocalGL3 p,
      (letI := LanglandsTunnell.TateLocal.localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 s g =
            (E.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))
          (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) (dualWhittakerFn3 (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)
              (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    :
    ∃ W₀ ∈ gl3CyclicSubspace (fun g : LocalGL3 p =>
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p (3 * B + Δ), ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
        ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k) ∧
      W₀ (iotaGL 1) = 1 := by
  classical
  set W₃ : LocalGL3 p → ℂ := fun g : LocalGL3 p =>
    ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g with hW₃
  have hW₃app : ∀ g, W₃ g = ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g := fun g => rfl

  have Lψ : psiLoc ψ p = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ := by
    have hψ' : ψ = NumberField.StandardAddChar.psiQ⁻¹ := by rw [← hψQ, inv_inv]
    ext x
    show ψ (NumberField.StandardAddChar.adeleSingleAt ℚ p x) = _
    rw [hψ', AddChar.inv_apply, AddChar.inv_apply, ← map_neg, ← NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt p (-x)]

  have Llaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃ := by
    intro x y z g
    rw [hW₃app, hW₃app, map_mul, det_upperUnipotent3, one_mul, ← Lψ, F.whittakerLoc_law p x y z g]
    ring

  have hB1 : 1 ≤ B := by omega
  have LU : ∃ U : Subgroup (LocalGL3 p), IsOpen (U : Set (LocalGL3 p)) ∧
      ∀ k ∈ U, ξ (Matrix.GeneralLinearGroup.det k) = 1 := by
    refine ⟨(ξ.comp Matrix.GeneralLinearGroup.det).ker, ?_, fun k hk => by rwa [MonoidHom.mem_ker] at hk⟩
    apply Subgroup.isOpen_of_one_mem_interior
    rw [mem_interior]
    obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p B
    refine ⟨{k : LocalGL3 p | Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det - 1) ≤ WithZero.exp (-(B : ℤ))}, ?_, ?_, ?_⟩
    · intro k hk
      rw [Set.mem_setOf_eq] at hk
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
      apply hξB.1
      have hexp : WithZero.exp (-(B : ℤ)) < 1 := by
        rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
      have hdet : ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = ((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det :=
        Matrix.GeneralLinearGroup.val_det_apply k
      refine ⟨?_, Or.inr ?_⟩
      · rw [hdet]
        have h1 : Valued.v ((((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det - 1) + 1) ≤
            max (Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det - 1)) (Valued.v (1 : p.adicCompletion ℚ)) := Valuation.map_add _ _ _
        rw [sub_add_cancel, map_one] at h1
        refine le_antisymm (h1.trans (max_le (hk.trans hexp.le) le_rfl)) ?_
        by_contra hlt
        rw [not_le] at hlt
        have h2 : Valued.v ((((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det) - (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det - 1)) ≤
            max (Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det)) (Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det - 1)) := Valuation.map_sub _ _ _
        rw [sub_sub_cancel, map_one] at h2
        exact absurd h2 (not_le.2 (max_lt hlt (hk.trans_lt hexp)))
      · rw [hdet]; exact hk
    · rw [← ht]
      exact (AdelicLevel.isOpen_setOf_valued_le (K := ℚ) p t ht0).preimage
        ((Units.continuous_val.matrix_det).sub continuous_const)
    · simp
  obtain ⟨U, hUo, hU⟩ := LU

  have Lsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃ (g * k) = W₃ g := by
    obtain ⟨Uv, hUvo, hUv⟩ := hsm
    refine ⟨U ⊓ Uv, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUo.inter hUvo
    · intro k hk g
      rw [hW₃app, hW₃app, map_mul, map_mul, Units.val_mul, hU k hk.1, Units.val_one, mul_one, hUv k hk.2 g]

  have Lne : W₃ ≠ 0 := by
    intro h0
    apply hne
    funext g
    have := congrFun h0 g
    rw [hW₃app, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left (Units.ne_zero _)

  have Lω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = (((ωp * ξ ^ 3) t : ℂˣ) : ℂ) * W₃ h := by
    intro t h
    rw [hW₃app, hW₃app, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hcent, map_mul, map_pow,
      MonoidHom.mul_apply, MonoidHom.pow_apply]
    push_cast
    ring

  let w₀ : GL (Fin 2) (p.adicCompletion ℚ) :=
    { val := !![0, 1; 1, 0], inv := !![0, 1; 1, 0]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  have htw := (LanglandsTunnell.RankinSelberg.gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq p ξ (F.whittakerLoc p) (fun _ => 0) w₀ rfl).1

  have Lirr : ∀ W ∈ gl3CyclicSubspace W₃, W ≠ 0 → W₃ ∈ gl3CyclicSubspace W := by
    intro W hW hW0
    have h1 : (fun g : LocalGL3 p => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W g) ∈
        gl3CyclicSubspace (F.whittakerLoc p) := (htw W).1 hW
    have h2 : (fun g : LocalGL3 p => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W g) ≠ 0 := by
      intro h0; apply hW0; funext g
      have := congrFun h0 g
      rw [Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left (inv_ne_zero (Units.ne_zero _))
    have h3 := hirr _ h1 h2

    have key := (LanglandsTunnell.RankinSelberg.gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq p ξ⁻¹ W (fun _ => 0) w₀ rfl).1 (F.whittakerLoc p)
    have e1 : (fun g : LocalGL3 p => ((ξ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g) =
        (fun g : LocalGL3 p => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W g) := by
      funext g; rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have e2 : (fun g : LocalGL3 p => ((ξ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * F.whittakerLoc p g) = W₃ := by
      funext g; rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv, hW₃app]
    rw [e1, e2] at key
    exact key.1 h3

  have Ladm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ Bs : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (Bs : Set (LocalGL3 p → ℂ)) := by
    intro Uv hUvo
    obtain ⟨Bs, hBs⟩ := hadm (U ⊓ Uv) (by rw [Subgroup.coe_inf]; exact hUo.inter hUvo)
    let T : (LocalGL3 p → ℂ) →ₗ[ℂ] (LocalGL3 p → ℂ) :=
      { toFun := fun f g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f g
        map_add' := fun f₁ f₂ => by funext g; simp only [Pi.add_apply]; ring
        map_smul' := fun c f => by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    refine ⟨Bs.image T, fun W hW hWk => ?_⟩
    set W' : LocalGL3 p → ℂ := fun g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W g with hW'
    have h1 : W' ∈ gl3CyclicSubspace (F.whittakerLoc p) := (htw W).1 hW
    have h2 : ∀ k ∈ U ⊓ Uv, ∀ g : LocalGL3 p, W' (g * k) = W' g := by
      intro k hk g
      simp only [hW', map_mul, hU k hk.1, mul_one, hWk k hk.2 g]
    have h3 := hBs W' h1 h2
    have hTW : T W' = W := by
      funext g
      show ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W g) = W g
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    rw [← hTW, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem h3

  have Lgauge : ∃ (Bg : ℝ) (tg : ℕ) (Cg : ℝ), ∀ h : LocalGL3 p,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg) → W₃ h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg →
        ‖W₃ h‖ ≤ Cg / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ tg) := by
    obtain ⟨Bg, tg, Cg, hg⟩ := LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero K _ ψ ν F hF0.1 hFg S' hgood p
    refine ⟨Bg, tg, Cg, fun h => ⟨fun hn => ?_, fun hy => ?_⟩⟩
    · rw [hW₃app, (hg h).1 hn, mul_zero]
    · rw [hW₃app, norm_mul, hξu, one_mul]; exact (hg h).2 hy

  have Lωu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖(((ωp * ξ ^ 3) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
      hωu, hξu, one_pow, one_mul]

  obtain ⟨W₀, hW₀mem, hW₀K, hW₀ι, hW₀supp, hW₀1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one p W₃ Llaw Lsm Lne (ωp * ξ ^ 3) Lω Lirr Ladm Lgauge Lωu E Ed ε ℓ hE1 hEd1 hε hℓ1 hωℓ h31
  exact ⟨W₀, hW₀mem, fun k hk g => hW₀K k (congruenceK1_antitone (𝓞 ℚ) ℚ p hℓ hk) g, hW₀ι, hW₀supp, hW₀1⟩

end S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_twist_whittakerLoc_congruenceK1_invariant_iotaGL_bump_of_conductor_le_ed3 (solution)
