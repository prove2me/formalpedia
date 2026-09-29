-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_localZeta31_fe_one_twist_coefficientFn_principalSeries3_of_exactConductor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/54effb0c-d4a9-5b3d-b8e3-33d694a526db

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_twist_det_localPackage
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localZeta31_fe_one_twist_coefficientFn_principalSeries3_of_exactConductor
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SpectralSide.instCompactSpaceMatrix ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LanglandsTunnell.CubicInduction.fnTwist3_apply ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open scoped Classical

namespace FE31PS3RAM

open Filter Topology

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem exists_eq_coefficientFn_of_mem_gl3CyclicSubspace {lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam))
    (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ f' : ↥(principalSeries3 p lam), W = coefficientFn Λ f' := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine ⟨⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩, ?_⟩
    funext g
    show coefficientFn Λ f (g * h) = _
    simp only [coefficientFn]
    congr 1
    apply Subtype.ext
    funext k
    simp [gl3AmbientRightTranslate, mul_assoc]
  | zero =>
    refine ⟨0, ?_⟩
    funext g
    simp only [coefficientFn, Pi.zero_apply]
    rw [← map_zero Λ]
    congr 1
  | add x y _ _ hx hy =>
    obtain ⟨f₁, rfl⟩ := hx
    obtain ⟨f₂, rfl⟩ := hy
    refine ⟨f₁ + f₂, ?_⟩
    funext g
    simp only [coefficientFn, Pi.add_apply]
    rw [← map_add Λ]
    congr 1
  | smul a x _ hx =>
    obtain ⟨f₁, rfl⟩ := hx
    refine ⟨a • f₁, ?_⟩
    funext g
    simp only [coefficientFn, Pi.smul_apply, smul_eq_mul]
    rw [← smul_eq_mul, ← map_smul Λ]
    congr 1

theorem eventually_valued_sub_le (c : p.adicCompletion ℚ) (n : ℕ) :
    ∀ᶠ y in 𝓝 c, Valued.v (y - c) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ : ∃ π : p.adicCompletion ℚ, Valued.v π = WithZero.exp (-(1 : ℤ)) := by
    refine ⟨(NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ), ?_⟩
    exact NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hπ0 : π ^ n ≠ 0 := by
    apply pow_ne_zero; intro h; rw [h, map_zero] at hπ; exact WithZero.coe_ne_zero.symm hπ
  have hvπn : Valued.v (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have h0 : Tendsto (fun y : p.adicCompletion ℚ => y - c) (𝓝 c) (𝓝 0) := by
    have := ((continuous_sub_right c).tendsto c)
    rwa [sub_self] at this
  filter_upwards [h0.eventually (eventually_valued_lt p hπ0)] with y hy
  rw [hvπn] at hy
  exact hy.le

theorem exists_isOpen_forall_coefficientFn_mul_eq {lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)) :
    ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, coefficientFn Λ f (g * k) = coefficientFn Λ f g := by
  obtain ⟨n, hn⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 p lam f f.2
  let Uv : Subgroup (LocalGL3 p) :=
    { carrier := {k | ∀ g : LocalGL3 p, coefficientFn Λ f (g * k) = coefficientFn Λ f g}
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      one_mem' := fun g => by rw [mul_one]
      inv_mem' := fun {a} ha g => by rw [← ha (g * a⁻¹), inv_mul_cancel_right] }
  have hfix : ∀ k : LocalGL3 p, (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))) → k ∈ Uv := by
    intro k hk g
    have hRk := hn k hk
    show Λ _ = Λ _
    congr 1
    apply Subtype.ext
    funext h
    show (f : LocalGL3 p → ℂ) (h * (g * k)) = (f : LocalGL3 p → ℂ) (h * g)
    have := congrFun hRk (h * g)
    rw [gl3AmbientRightTranslate_apply] at this
    rw [← mul_assoc]; exact this
  refine ⟨Uv, ?_, fun k hk g => hk g⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hev : ∀ᶠ (k : LocalGL3 p) in 𝓝 (1 : LocalGL3 p), ∀ i j : Fin 3,
      Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; intro j
    have hc : Continuous fun k : LocalGL3 p => (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j :=
      Units.continuous_val.matrix_elem i j
    exact (hc.tendsto 1).eventually
      (eventually_valued_sub_le p (((1 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) n)
  exact Filter.mem_of_superset hev (fun k hk => hfix k hk)

theorem coefficientFn_scalar_mul {lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam))
    (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p) :
    coefficientFn Λ f (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
      (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) * coefficientFn Λ f h := by
  have hscal : Matrix.GeneralLinearGroup.scalar (Fin 3) t = diagonal3 p (fun _ => t) := by
    apply Units.ext; simp [Matrix.GeneralLinearGroup.scalar]
  have hcomm : ∀ k : LocalGL3 p, k * Matrix.GeneralLinearGroup.scalar (Fin 3) t =
      Matrix.GeneralLinearGroup.scalar (Fin 3) t * k := by
    intro k; apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar]
    ext i j; simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  have h1 : halfModulus3 p (fun _ => t) = 1 := by
    simp only [halfModulus3]
    rw [div_self (norm_ne_zero_iff.2 (Units.ne_zero t))]; simp
  have h2 : torusChar3 p lam (fun _ => t) = (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) := by
    simp only [torusChar3, Fin.prod_univ_three, MonoidHom.mul_apply, Units.val_mul]
  have key : (⟨gl3AmbientRightTranslate (R := ℂ) (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) (f : LocalGL3 p → ℂ),
        rightTranslate_mem_principalSeries3 f.2 (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h)⟩ : ↥(principalSeries3 p lam)) =
      (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) • (⟨gl3AmbientRightTranslate (R := ℂ) h (f : LocalGL3 p → ℂ),
        rightTranslate_mem_principalSeries3 f.2 h⟩ : ↥(principalSeries3 p lam)) := by
    apply Subtype.ext
    funext k
    show (f : LocalGL3 p → ℂ) (k * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h)) =
      (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) * (f : LocalGL3 p → ℂ) (k * h)
    rw [← mul_assoc, hcomm k, mul_assoc, hscal, apply_diagonal3_mul_of_mem_principalSeries3 f.2, h2, h1, mul_one]
  show Λ _ = (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) * Λ _
  rw [key, map_smul, smul_eq_mul]

theorem mem_localMaximalCompact3_of_valued_sub_le (n : ℕ) (k : LocalGL3 p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ)))
    (hk' : ∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hone : ∀ i j : Fin 3, Valued.v ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have hexp : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)),
      (∀ i j : Fin 3, Valued.v (M i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ))) →
      ∀ i j : Fin 3, Valued.v (M i j) ≤ 1 := by
    intro M hM i j
    have h := Valuation.map_add Valued.v (M i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j)
      ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j)
    rw [sub_add_cancel] at h
    exact h.trans (max_le ((hM i j).trans hexp) (hone i j))
  exact ⟨key _ hk, key _ hk'⟩

theorem ker_mem_nhds_one_of_forall_higherUnitsAt (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (hχc : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, χ u = 1) :
    ((MonoidHom.ker χ : Subgroup (p.adicCompletion ℚ)ˣ) : Set (p.adicCompletion ℚ)ˣ) ∈ nhds (1 : (p.adicCompletion ℚ)ˣ) := by
  have hb : 1 < (Ideal.absNorm p.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  set r : ℝ := (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero p) (WithZero.exp (-(c : ℤ))) : ℝ)
    with hr
  have hr0 : 0 < r := by
    rw [hr]; exact_mod_cast WithZeroMulInt.toNNReal_pos (NumberField.HeightOneSpectrum.absNorm_ne_zero p) WithZero.exp_ne_zero
  have hS : (fun u : (p.adicCompletion ℚ)ˣ => (u : p.adicCompletion ℚ)) ⁻¹' Metric.ball 1 r ∈
      nhds (1 : (p.adicCompletion ℚ)ˣ) :=
    (Metric.isOpen_ball.preimage Units.continuous_val).mem_nhds (by
      show ((1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈ Metric.ball 1 r
      rw [Units.val_one]; exact Metric.mem_ball_self hr0)
  refine Filter.mem_of_superset hS ?_
  intro u hu
  have hu' : ‖(u : p.adicCompletion ℚ) - 1‖ < r := by
    have := hu
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at this
    exact this
  have hlt : Valued.v ((u : p.adicCompletion ℚ) - 1) < WithZero.exp (-(c : ℤ)) := by
    rw [NumberField.FinitePlace.norm_def, hr] at hu'
    exact (WithZeroMulInt.toNNReal_strictMono hb).lt_iff_lt.mp (by exact_mod_cast hu')
  have hv1 : Valued.v (u : p.adicCompletion ℚ) = 1 := by
    have h' : Valued.v ((u : p.adicCompletion ℚ) - 1) < Valued.v (1 : p.adicCompletion ℚ) := by
      rw [map_one]
      refine lt_of_lt_of_le hlt ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    rw [Valuation.map_eq_of_sub_lt Valued.v h', map_one]
  have hmem : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c := by
    refine ⟨hv1, ?_⟩
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr hlt.le
  exact hχc u hmem

theorem exists_hasConductorExponentAt_of_forall_higherUnitsAt (ρ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (n : ℕ)
    (hρ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p n, ρ u = 1) :
    ∃ c ≤ n, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ρ c := by
  classical
  have hex : ∃ c, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, ρ u = 1 := ⟨n, hρ⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hρ, Nat.find_spec hex, fun m hm => ?_⟩
  by_contra hcon
  apply Nat.find_min hex hm
  intro u hu
  by_contra hne
  exact hcon ⟨u, hu, hne⟩

theorem exists_isOpen_subgroup_forall_inv_eq_one (lam0 χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlam0 : IsLocallyConstant lam0) (d : ℕ)
    (h : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam0 * χ⁻¹) u = 1) :
    ∃ U₀ : Subgroup (p.adicCompletion ℚ)ˣ, IsOpen (U₀ : Set (p.adicCompletion ℚ)ˣ) ∧ ∀ u ∈ U₀, χ⁻¹ u = 1 := by
  have h1 := ker_mem_nhds_one_of_forall_higherUnitsAt p (lam0 * χ⁻¹) d h
  have h2 : {u : (p.adicCompletion ℚ)ˣ | lam0 u = lam0 1} ∈ nhds (1 : (p.adicCompletion ℚ)ˣ) :=
    (hlam0.isOpen_fiber (lam0 1)).mem_nhds rfl
  have h3 : ((MonoidHom.ker χ⁻¹ : Subgroup (p.adicCompletion ℚ)ˣ) : Set (p.adicCompletion ℚ)ˣ) ∈
      nhds (1 : (p.adicCompletion ℚ)ˣ) := by
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro u ⟨hu1, hu2⟩
    have hu1' : (lam0 * χ⁻¹) u = 1 := MonoidHom.mem_ker.mp hu1
    have hu2' : lam0 u = 1 := by
      have : lam0 u = lam0 1 := hu2
      rw [this, map_one]
    show u ∈ MonoidHom.ker χ⁻¹
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mul_apply, hu2', one_mul] at hu1'
    exact hu1'
  exact ⟨MonoidHom.ker χ⁻¹, Subgroup.isOpen_of_mem_nhds _ h3, fun u hu => MonoidHom.mem_ker.mp hu⟩

theorem exists_JS85_datum_of_frame
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hlamu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (W2 : LocalGL3 p → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (d : ℕ)
    (hshallow : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1)
    (hlev₂ : ∃ W' ∈ gl3CyclicSubspace W2, W' ≠ 0 ∧
        ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
              (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
          ∀ g : LocalGL3 p,
            ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g) :
    ∃ (W₀ : LocalGL3 p → ℂ) (ω₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ),
      W2 ∈ gl3CyclicSubspace (fun x : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x) ∧
      IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀ ∧
      W₀ ≠ 0 ∧
      HasWhittakerMultOne (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀ ∧
      (∀ F ∈ gl3CyclicSubspace W₀, F ≠ 0 → W₀ ∈ gl3CyclicSubspace F) ∧
      (∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
        ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace W₀,
          (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ))) ∧
      (∀ z : (p.adicCompletion ℚ)ˣ, ‖((ω₀ z : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₀ t : ℂˣ) : ℂ) * W₀ h) ∧
      (∀ k : LocalGL3 p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        (∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) ∧
      (∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, ω₀ u = 1) := by
  obtain ⟨Λ, f, hΛ, rfl⟩ := hmem
  obtain ⟨W', hW'mem, hW'ne, hW'lev⟩ := hlev₂
  obtain ⟨f', rfl⟩ := exists_eq_coefficientFn_of_mem_gl3CyclicSubspace p Λ f W' hW'mem

  have hW'law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (coefficientFn Λ f') :=
    isGL3PsiWhittakerFn_coefficientFn hΛ f'
  have hW'sm := exists_isOpen_forall_coefficientFn_mul_eq p Λ f'
  have hW'cen : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      coefficientFn Λ f' (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        (((lam 0 * lam 1 * lam 2) t : ℂˣ) : ℂ) * coefficientFn Λ f' h := coefficientFn_scalar_mul p Λ f'
  have hW'irr : ∀ F ∈ gl3CyclicSubspace (coefficientFn Λ f'), F ≠ 0 → coefficientFn Λ f' ∈ gl3CyclicSubspace F :=
    LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn p lam hlamu Λ f
      (coefficientFn Λ f') hW'mem
  have hW'adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ F ∈ gl3CyclicSubspace (coefficientFn Λ f'),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)) := by
    intro Uv hUv
    obtain ⟨B, hB⟩ := LanglandsTunnell.CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen p lam Λ Uv hUv
    refine ⟨B, fun F hF hFinv => ?_⟩
    obtain ⟨f'', rfl⟩ := exists_eq_coefficientFn_of_mem_gl3CyclicSubspace p Λ f' F hF
    exact hB f'' hFinv
  have hψne : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ ≠ 1 := fun h =>
    LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p (inv_eq_one.mp h)
  have hW'mult : HasWhittakerMultOne (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (coefficientFn Λ f') :=
    LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace p _ hψne _
      hW'ne hW'irr hW'sm hW'adm
  have hω₃u : ∀ z : (p.adicCompletion ℚ)ˣ, ‖(((lam 0 * lam 1 * lam 2) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_mul, hlamu]
    norm_num

  obtain ⟨U₀, hU₀o, hU₀⟩ := exists_isOpen_subgroup_forall_inv_eq_one p (lam 0) χ (hlam 0) d (hshallow 0)
  have hχinvu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((χ⁻¹ z : ℂˣ) : ℂ)‖ = 1 := fun z => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχu, inv_one]
  set W₀ : LocalGL3 p → ℂ := fun x => ((χ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * coefficientFn Λ f' x
    with hW₀def
  have hW'eq : (fun x : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x) = coefficientFn Λ f' := by
    funext x
    simp only [hW₀def]
    rw [← mul_assoc, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_mul]
  obtain ⟨hPa, hPb, hPc, hPd⟩ := LanglandsTunnell.CubicInduction.twist_det_localPackage p
    (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ χ⁻¹ U₀ hU₀o hU₀ hχinvu (coefficientFn Λ f')
  have hW₀adm := hPa hW'adm
  have hW₀mult := hPb hW'mult
  have hW₀sm := hPc hW'sm
  obtain ⟨hωvu, hW₀cen⟩ := hPd (lam 0 * lam 1 * lam 2) hω₃u hW'cen
  obtain ⟨hT1, hT2, hT3, -⟩ := LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det p χ⁻¹ (coefficientFn Λ f')
  have hW₀ne : W₀ ≠ 0 := fun h0 => hW'ne (hT3.mp h0)
  have hW₀irr : ∀ F ∈ gl3CyclicSubspace W₀, F ≠ 0 → W₀ ∈ gl3CyclicSubspace F := by
    intro F hF hF0
    obtain ⟨F', hF'mem, rfl⟩ := hT2 F hF
    have hF'0 : F' ≠ 0 := by
      rintro rfl; apply hF0; funext x; simp
    exact (LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det p χ⁻¹ F').1 _ (hW'irr F' hF'mem hF'0)
  have hdetN : ∀ x y z : p.adicCompletion ℚ, Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 p) = 1 := by
    intro x y z
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Matrix.det_fin_three]
    simp
  have hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀ := by
    intro x y z g
    simp only [hW₀def]
    rw [map_mul, hdetN, one_mul, hW'law x y z g, mul_left_comm]
  have hW₀lev : ∀ k : LocalGL3 p,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      (∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g := by
    intro k hk hk' g
    have hmem := mem_localMaximalCompact3_of_valued_sub_le p d k hk hk'
    have h := hW'lev k hmem hk g
    simp only [hW₀def]
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    exact h
  have hω₀d : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam 0 * lam 1 * lam 2 * χ⁻¹ ^ 3) u = 1 := by
    intro u hu
    have h0 := hshallow 0 u hu
    have h1 := hshallow 1 u hu
    have h2 := hshallow 2 u hu
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at h0 h1 h2
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply]
    have h0' := congrArg Units.val h0
    have h1' := congrArg Units.val h1
    have h2' := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one] at h0' h1' h2'
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_one]
    calc ((lam 0 u : ℂˣ) : ℂ) * ((lam 1 u : ℂˣ) : ℂ) * ((lam 2 u : ℂˣ) : ℂ) * (((χ u : ℂˣ) : ℂ))⁻¹ ^ 3
        = (((lam 0 u : ℂˣ) : ℂ) * (((χ u : ℂˣ) : ℂ))⁻¹) * (((lam 1 u : ℂˣ) : ℂ) * (((χ u : ℂˣ) : ℂ))⁻¹) *
            (((lam 2 u : ℂˣ) : ℂ) * (((χ u : ℂˣ) : ℂ))⁻¹) := by ring
      _ = 1 := by rw [h0', h1', h2', one_mul, one_mul]
  have hW2cyc : coefficientFn Λ f ∈
      gl3CyclicSubspace (fun x : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x) := by
    rw [hW'eq]
    exact LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn p lam hlamu Λ f
      (coefficientFn Λ f) (Submodule.subset_span ⟨1, by funext x; simp⟩) _ hW'mem hW'ne
  exact ⟨W₀, lam 0 * lam 1 * lam 2 * χ⁻¹ ^ 3, hW2cyc, hW₀law, hW₀ne, hW₀mult, hW₀irr, hW₀sm, hW₀adm, hωvu,
    hW₀cen, hW₀lev, hω₀d⟩

set_option maxHeartbeats 1600000 in

theorem main
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hlamu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (W2 : LocalGL3 p → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f)
    (hW2ne : W2 ≠ 0)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (d : ℕ) (hd : 0 < d)
    (hshallow : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1)

    (hlev₂ : ∃ W' ∈ gl3CyclicSubspace W2, W' ≠ 0 ∧
        ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
              (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
          ∀ g : LocalGL3 p,
            ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (hdB : 2 * d + 1 ≤ B) :
    letI := localBorel ℚ p
    ∃ ε : ℂ, ε ≠ 0 ∧ ∀ g : LocalGL3 p,
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 s g = P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 (1 - s) g =
            (ε * (Ideal.absNorm p.asIdeal : ℂ) ^ (((3 * B : ℕ) : ℂ) * (1 / 2 - s))) * P s := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  obtain ⟨W₀, ω₀, hW2cyc, hW₀law, hW₀ne, hW₀mult, hW₀irr, hW₀sm, hW₀adm, hω₀u, hW₀cen, hW₀lev, hω₀d⟩ :=
    exists_JS85_datum_of_frame p lam hlam hlamu W2 hmem χ hχu d hshallow hlev₂

  have hL1 :=
    LanglandsTunnell.CubicInduction.forall_localZetaDual31_eq_mul_localZeta30_and_exists_localZeta30_ne_zero_of_ne_zero_of_principalCongruence_of_two_mul_le
      p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ rfl W₀ hW₀law hW₀ne hW₀mult hW₀irr hW₀sm hW₀adm ω₀ hω₀u hW₀cen
      d hd hW₀lev ξ B hξB (hξu _) (by omega)
  obtain ⟨σ₀, σ₁, hall, -⟩ := hL1

  set C : ℂ := ((ω₀ (-1) : ℂˣ) : ℂ) * ((ξ (-1) : ℂˣ) : ℂ) *
      (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω₀ * ξ) * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p ξ ^ 2)
    with hCdef
  have hCne : C ≠ 0 := by
    have hdB' : d ≤ B := by omega
    have hωξ1 : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p B, (ω₀ * ξ) u = 1 := by
      intro u hu
      rw [MonoidHom.mul_apply, hω₀d u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p hdB' hu), hξB.1 u hu,
        one_mul]
    obtain ⟨c, -, hc⟩ := exists_hasConductorExponentAt_of_forall_higherUnitsAt p (ω₀ * ξ) B hωξ1
    have hωξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖(((ω₀ * ξ) x : ℂˣ) : ℂ)‖ = 1 := fun x => by
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hω₀u, hξu, one_mul]
    have hε1 := LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt ℚ p (ω₀ * ξ) c hc hωξu
    have hε2 := LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt ℚ p ξ B hξB hξu
    have hne1 : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω₀ * ξ) ≠ 0 := fun h => by
      rw [h, norm_zero] at hε1; exact zero_ne_one hε1
    have hne2 : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p ξ ≠ 0 := fun h => by
      rw [h, norm_zero] at hε2; exact zero_ne_one hε2
    rw [hCdef]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (mul_ne_zero hne1 (pow_ne_zero 2 hne2))

  set V : LocalGL3 p → ℂ := fun x => ((ξ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x with hVdef
  have h1ξ : (1 : (p.adicCompletion ℚ)ˣ →* ℂˣ) * ξ = ξ := one_mul ξ
  have h31 : ∀ g : LocalGL3 p,
      (letI := localBorel ℚ p
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V 1 s g =
            ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 V) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              V 1 (1 - s) g =
            ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((C * (Ideal.absNorm p.asIdeal : ℂ) ^ (((3 * B : ℕ) : ℂ) * (1 / 2 - s))) * P s)) := by
    intro g
    obtain ⟨P, ⟨Q, m, hP⟩, hc0, hz0, hc1, hz1⟩ := hall g
    obtain ⟨hT30, hTc30, hT31, hTc31⟩ := LanglandsTunnell.CubicInduction.localZeta30_localZetaDual31_twist_det p
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) W₀ ξ 1 g
    simp only [h1ξ, inv_one] at hT30 hTc30 hT31 hTc31
    refine ⟨fun s => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * P s, σ₀, σ₁,
      ⟨Polynomial.C (((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) * Q, 1, m, one_ne_zero, fun s => ?_⟩,
      (hTc30 σ₀).mpr hc0, fun s hs => ?_, (hTc31 σ₁).mpr hc1, fun s hs => ?_⟩
    · beta_reduce
      rw [Polynomial.eval_one, mul_one, Polynomial.eval_mul, Polynomial.eval_C, hP s, mul_assoc]
    · beta_reduce
      rw [hT30 s, hz0 s hs, Polynomial.eval_one, inv_one, one_mul]
    · beta_reduce
      rw [hT31 (1 - s), hz1 s hs, Polynomial.eval_one, inv_one, one_mul, hCdef]
      push_cast
      ring

  have hcycV : (fun g : LocalGL3 p =>
      ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) ∈
      gl3CyclicSubspace V := by
    have h : (fun x : LocalGL3 p => (((ξ * χ⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W2 x) ∈
        gl3CyclicSubspace (fun x : LocalGL3 p => (((ξ * χ⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) *
          (((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x)) :=
      (LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det p (ξ * χ⁻¹)
        (fun x : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x)).1 W2 hW2cyc
    have e1 : (fun x : LocalGL3 p => (((ξ * χ⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W2 x) =
        (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) := by
      funext x
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have e2 : (fun x : LocalGL3 p => (((ξ * χ⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) *
        (((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₀ x)) = V := by
      funext x
      simp only [hVdef]
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc,
        inv_mul_cancel_left₀ (Units.ne_zero _)]
    rw [e1, e2] at h
    exact h
  have hTr :=
    LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall p
      V 1 1 C (3 * B) h31 _ hcycV
  refine ⟨C, hCne, fun g => ?_⟩
  obtain ⟨P, σ₀', σ₁', hrat, hc0, hz0, hc1, hz1⟩ := hTr g
  refine ⟨P, σ₀', σ₁', hrat, hc0, fun s hs => ?_, hc1, fun s hs => ?_⟩
  · rw [hz0 s hs, Polynomial.eval_one, inv_one, one_mul]
  · rw [hz1 s hs, Polynomial.eval_one, inv_one, one_mul]

end FE31PS3RAM

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hlamu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (W2 : LocalGL3 p → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧ W2 = coefficientFn Λ f)
    (hW2ne : W2 ≠ 0)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (d : ℕ) (hd : 0 < d)
    (hshallow : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1)

    (hlev₂ : ∃ W' ∈ gl3CyclicSubspace W2, W' ≠ 0 ∧
        ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
          (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
              (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
          ∀ g : LocalGL3 p,
            ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (hdB : 2 * d + 1 ≤ B) :
    letI := localBorel ℚ p
    ∃ ε : ℂ, ε ≠ 0 ∧ ∀ g : LocalGL3 p,
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 s g = P s) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              (fun g : LocalGL3 p =>
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W2 g) 1 (1 - s) g =
            (ε * (Ideal.absNorm p.asIdeal : ℂ) ^ (((3 * B : ℕ) : ℂ) * (1 / 2 - s))) * P s :=
  FE31PS3RAM.main p lam hlam hlamu W2 hmem hW2ne χ hχu d hd hshallow hlev₂ ξ hξu B hξB hdB

end S_LanglandsTunnell_RankinSelberg_exists_forall_localZeta31_fe_one_twist_coefficientFn_principalSeries3_of_exactConductor
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localZeta31_fe_one_twist_coefficientFn_principalSeries3_of_exactConductor (solution)
