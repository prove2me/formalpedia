-- Prove2me | solution 1 for LanglandsTunnell.fnTwist_gaussSumFn_isSmoothCuspData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/149b0ec9-af36-5a68-9dfa-5baa21b2c7f9

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData

set_option Elab.async false

p2m_open "NumberField AutomorphicForm P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.AutomorphicForm"

section M4aP5_TwistRealization
open IsDedekindDomain NumberField MeasureTheory Matrix
p2m_open "AutomorphicForm P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.AutomorphicForm AutomorphicForm.SmoothCusp FLT.SmoothVectors"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "fnTwist fnTwist_apply chiDet_centralScalar_mul twistedCentralChar isLsXiFunction_fnTwist isSmoothVector_rightTranslationFn_mul isKfSmooth_fnTwist finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_const CarrierPins AdelicGL2 centralScalar IsIdeleClassChar IsUnitaryChar IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsCuspidalFn GaussTwist.gaussWt GaussTwist.gaussTrans GaussTwist.gaussSumFn IsBoundedGenuineFn isBoundedGenuineFn_iff whittakerCoefficient WhittakerCoefficientIntegrable"
namespace TwistRealization
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

private theorem det_unipotentGL2 (q : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  ring

private theorem chiDet_unipotent_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (q : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F η (unipotentGL2 q * g) = chiDet (𝓞 F) F η g := by
  show ((η (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) : ℂˣ) : ℂ) = _
  rw [map_mul, det_unipotentGL2, one_mul]
  rfl

private theorem isCuspidalFn_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {nS : MeasurableSpace (AdeleRing (𝓞 F) F)} (ν : Measure (AdeleRing (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : @IsCuspidalFn _ nS _ _ ν unipotentGL2 φ) :
    @IsCuspidalFn _ nS _ _ ν unipotentGL2 (fnTwist F η φ) := by
  intro g
  have hpt : ∀ q : AdeleRing (𝓞 F) F,
      constantTermIntegrand unipotentGL2 (fnTwist F η φ) g q
        = chiDet (𝓞 F) F η g * constantTermIntegrand unipotentGL2 φ g q := by
    intro q
    unfold constantTermIntegrand
    show chiDet (𝓞 F) F η (unipotentGL2 q * g) * φ (unipotentGL2 q * g) = _
    rw [chiDet_unipotent_mul]
  unfold constantTerm
  calc ∫ q, constantTermIntegrand unipotentGL2 (fnTwist F η φ) g q ∂ν
      = ∫ q, chiDet (𝓞 F) F η g * constantTermIntegrand unipotentGL2 φ g q ∂ν := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = chiDet (𝓞 F) F η g * ∫ q, constantTermIntegrand unipotentGL2 φ g q ∂ν :=
        integral_const_mul _ _
    _ = 0 := by rw [show (∫ q, constantTermIntegrand unipotentGL2 φ g q ∂ν) = 0 from hφ g, mul_zero]

end AutomorphicForm.TwistRealization
end M4aP5_TwistRealization

section M4aP7_LevelMono
noncomputable section
p2m_open "NumberField AutomorphicForm P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam"
open AutomorphicForm.SmoothCusp

namespace P7LevelMono

section Rebase

variable {G : Type*} [Group G]

end Rebase

section Antitone

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

end Antitone

section Key

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

end Key

section Transport

variable (F : Type) [Field F] [NumberField F]

end Transport

section HU

variable (F : Type) [Field F] [NumberField F]

end HU

section ArchTrim

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem matrix_eq_of_parts {M M' : Matrix (Fin 2) (Fin 2) (AdeleRing R K)}
    (ha : (adeleArch R K).mapMatrix M = (adeleArch R K).mapMatrix M')
    (hf : (adeleFin R K).mapMatrix M = (adeleFin R K).mapMatrix M') : M = M' := by
  ext i j
  exact Prod.ext (congrFun (congrFun ha i) j) (congrFun (congrFun hf i) j)

end ArchTrim

section ArchTrimProduction

variable (F : Type) [Field F] [NumberField F]

end ArchTrimProduction

section FinSurgery

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private def adeleOn (S : Finset (HeightOneSpectrum R)) [DecidablePred (· ∈ S)]
    (y : (w : HeightOneSpectrum R) → w.adicCompletion K) : FiniteAdeleRing R K :=
  ⟨fun w => if w ∈ S then y w else 0,
    S.eventually_cofinite_notMem.mono fun w hw => by
      dsimp only
      rw [if_neg hw]
      exact (w.adicCompletionIntegers K).zero_mem⟩

private def finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j =>
    (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, m i j) : AdeleRing R K)

private theorem mapMatrix_adeleArch_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleArch R K).mapMatrix (finPair m) = 1 := by
  ext i j
  rfl

private theorem mapMatrix_adeleFin_finPair (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    (adeleFin R K).mapMatrix (finPair m) = m := by
  ext i j
  rfl

private theorem finPair_one : finPair (R := R) (K := K) 1 = 1 :=
  matrix_eq_of_parts (by rw [mapMatrix_adeleArch_finPair, map_one])
    (by rw [mapMatrix_adeleFin_finPair, map_one])

private theorem finPair_mul (m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    finPair m * finPair m' = finPair (m * m') :=
  matrix_eq_of_parts
    (by rw [map_mul, mapMatrix_adeleArch_finPair, mapMatrix_adeleArch_finPair,
      mapMatrix_adeleArch_finPair, mul_one])
    (by rw [map_mul, mapMatrix_adeleFin_finPair, mapMatrix_adeleFin_finPair,
      mapMatrix_adeleFin_finPair])

private def finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : GL (Fin 2) (AdeleRing R K) where
  val := finPair (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  inv := finPair
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
  val_inv := by rw [finPair_mul, Units.mul_inv, finPair_one]
  inv_val := by rw [finPair_mul, Units.inv_mul, finPair_one]

private theorem glArch_finLift (g : GL (Fin 2) (FiniteAdeleRing R K)) : glArch R K (finLift g) = 1 := by
  ext i j
  rw [Units.val_one]
  rfl

end FinSurgery

section FinSurgeryProduction

variable (F : Type) [Field F] [NumberField F]

end FinSurgeryProduction

end P7LevelMono

section Prints
end Prints

end
end M4aP7_LevelMono

section M4aP7_LevelMonoFurniture2
set_option maxSynthPendingDepth 3

noncomputable section
p2m_open "NumberField AutomorphicForm P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam"

namespace P7LevelMono

section LocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

private theorem units_map_quotient_maximalIdeal_pow_surjective (n : ℕ) :
    Function.Surjective
      (Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hsub : Subsingleton (A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [hn, pow_zero, Ideal.one_eq_top])
    exact fun y => ⟨1, Subsingleton.elim _ _⟩
  · refine IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective ?_
    refine isLocalHom_of_le_jacobson_bot _ ?_
    calc (IsLocalRing.maximalIdeal A) ^ n
        ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self hn.ne'
      _ = Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

private def unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : Aˣ :=
  Function.surjInv (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem unitQuotLift_spec (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Units.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n)).toMonoidHom
      (unitQuotLift A n x) = x :=
  Function.surjInv_eq (units_map_quotient_maximalIdeal_pow_surjective A n) x

private theorem mk_coe_unitQuotLift (n : ℕ) (x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) (unitQuotLift A n x : A)
      = ((x : (A ⧸ (IsLocalRing.maximalIdeal A) ^ n)ˣ) : A ⧸ (IsLocalRing.maximalIdeal A) ^ n) :=
  congrArg Units.val (unitQuotLift_spec A n x)

end LocalRing

section IdealBound

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, γ = WithZero.exp m := ⟨WithZero.log γ, (WithZero.exp_log h0).symm⟩
    subst hm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.mpr (by omega)

end IdealBound

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

private def localUnif : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_localUnif : Valued.v (localUnif K v) = WithZero.exp (-1 : ℤ) := by
  unfold localUnif
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem valued_localUnif_inv_pow (n : ℕ) :
    Valued.v ((localUnif K v)⁻¹ ^ n) = WithZero.exp (n : ℤ) := by
  rw [map_pow, map_inv₀, valued_localUnif, ← WithZero.exp_neg, neg_neg]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, WithZero.exp_add]

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) :=
  Valuation.valuationSubring.integers _

private theorem valued_coe_eq_one_of_isUnit {x : v.adicCompletionIntegers K} (hx : IsUnit x) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (integers_adicCompletionIntegers K v).one_of_isUnit hx

private theorem isUnit_of_valued_coe_eq_one {x : v.adicCompletionIntegers K}
    (hx : Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) = 1) : IsUnit x :=
  (integers_adicCompletionIntegers K v).isUnit_of_one' hx

private theorem valued_units_coe (r : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (((r : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 :=
  valued_coe_eq_one_of_isUnit K v r.isUnit

private theorem valued_coe_le_exp_neg_one_of_mem_maximalIdeal {x : v.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  refine le_exp_neg_one_of_lt_one (lt_of_le_of_ne
    ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2) fun h => ?_)
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx))
    (isUnit_of_valued_coe_eq_one K v h)

private theorem valued_coe_le_exp_neg_of_mem_maximalIdeal_pow {n : ℕ} {x : v.adicCompletionIntegers K}
    (hx : x ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      ≤ WithZero.exp (-(n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  | succ n ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun m hm y hy => ?_) (fun y z hy hz => ?_)
      · rw [show ((m * y : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (m : v.adicCompletion K) * y from rfl, map_mul, Nat.cast_succ, neg_add,
          WithZero.exp_add]
        exact mul_le_mul' (ih hm) (valued_coe_le_exp_neg_one_of_mem_maximalIdeal K v hy)
      · rw [show ((y + z : v.adicCompletionIntegers K) : v.adicCompletion K)
            = (y : v.adicCompletion K) + z from rfl]
        exact Valuation.map_add_le _ hy hz

private theorem valued_compat_le_one_core (n : ℕ) {α ρ ρ' d : v.adicCompletion K}
    (hρ' : Valued.v ρ' = 1)
    (h1 : Valued.v (α * ρ - ρ') ≤ WithZero.exp (-(n : ℤ)))
    (hd : Valued.v (d - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (α * (ρ * (localUnif K v)⁻¹ ^ n) - (ρ' * (localUnif K v)⁻¹ ^ n) * d) ≤ 1 := by
  have key : α * (ρ * (localUnif K v)⁻¹ ^ n) - (ρ' * (localUnif K v)⁻¹ ^ n) * d
      = (localUnif K v)⁻¹ ^ n * ((α * ρ - ρ') - ρ' * (d - 1)) := by ring
  have h2 : Valued.v (ρ' * (d - 1)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [map_mul, hρ', one_mul]; exact hd
  rw [key, map_mul, valued_localUnif_inv_pow]
  calc WithZero.exp (n : ℤ) * Valued.v ((α * ρ - ρ') - ρ' * (d - 1))
      ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul_right (Valuation.map_sub_le _ h1 h2) _
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

private theorem valued_coe_mul_coe_sub_coe_le (n : ℕ) (aInt r r' : (v.adicCompletionIntegers K)ˣ)
    (hr' : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (r' : v.adicCompletionIntegers K)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        ((aInt : v.adicCompletionIntegers K) * r)) :
    Valued.v ((((aInt : v.adicCompletionIntegers K) : v.adicCompletion K))
        * (((r : v.adicCompletionIntegers K) : v.adicCompletion K))
      - (((r' : v.adicCompletionIntegers K) : v.adicCompletion K)))
      ≤ WithZero.exp (-(n : ℤ)) := by
  have h := valued_coe_le_exp_neg_of_mem_maximalIdeal_pow K v (Ideal.Quotient.eq.mp hr'.symm)
  rwa [AddSubgroupClass.coe_sub, MulMemClass.coe_mul] at h

private theorem valued_compat_le_one (n : ℕ) (aInt : (v.adicCompletionIntegers K)ˣ)
    {a : v.adicCompletion K}
    (ha : a = (((aInt : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)
      : v.adicCompletion K))
    (r r' : (v.adicCompletionIntegers K)ˣ)
    (hr' : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (r' : v.adicCompletionIntegers K)
      = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        ((aInt : v.adicCompletionIntegers K) * r))
    {d : v.adicCompletion K} (hd : Valued.v (d - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (a * ((((r : v.adicCompletionIntegers K) : v.adicCompletion K))
          * (localUnif K v)⁻¹ ^ n)
      - ((((r' : v.adicCompletionIntegers K) : v.adicCompletion K)) * (localUnif K v)⁻¹ ^ n)
          * d) ≤ 1 := by
  subst ha
  exact valued_compat_le_one_core K v n (valued_units_coe K v r')
    (valued_coe_mul_coe_sub_coe_le K v n aInt r r' hr') hd

end Local

section Production

variable (F : Type) [Field F] [NumberField F]

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 w = WithZero.exp (-(HeckeCharacter.idealMultiplicity F w 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 w

end Production

end P7LevelMono

section Prints
end Prints

end
end M4aP7_LevelMonoFurniture2

section M4aP7_RamifiedTwist
noncomputable section
p2m_open "NumberField AutomorphicForm P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData.AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam"
open AutomorphicForm.SmoothCusp

namespace P7RamTwist

open AutomorphicForm.GaussTwist
variable (F : Type) [Field F] [NumberField F]

open P7LevelMono
open scoped Classical
open FLT.SmoothVectors AutomorphicForm.TwistRealization MeasureTheory

set_option maxSynthPendingDepth 3

private def gaussTwistFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fnTwist F η (gaussSumFn F η 𝔣 φ)

private theorem continuous_chiDet_of_continuous (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hcont : Continuous η) : Continuous (chiDet (𝓞 F) F η) :=
  Units.continuous_val.comp (hcont.comp Matrix.GeneralLinearGroup.continuous_det)

private def modulusNhd (𝔣 : Ideal (𝓞 F)) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {x | (↑x : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F
     ∧ ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F
     ∧ (↑x : AdeleRing (𝓞 F) F).2 - 1 ∈ idealBall (𝓞 F) F 𝔣}

private theorem isOpen_modulusNhd (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) : IsOpen (modulusNhd F 𝔣) :=
  ((isOpen_integralFiniteAdeles (𝓞 F) F).preimage
      (continuous_snd.comp Units.continuous_val)).inter
    (((isOpen_integralFiniteAdeles (𝓞 F) F).preimage
      (continuous_snd.comp Units.continuous_coe_inv)).inter
    ((isOpen_idealBall (𝓞 F) F h𝔣).preimage
      ((continuous_snd.comp Units.continuous_val).sub continuous_const)))

private theorem one_mem_modulusNhd (𝔣 : Ideal (𝓞 F)) : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ modulusNhd F 𝔣 :=
  ⟨fun v => one_mem _, by rw [inv_one]; exact fun v => one_mem _,
   by rw [show ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
            = (1 : FiniteAdeleRing (𝓞 F) F) from rfl, sub_self];
      exact zero_mem_idealBall 𝔣⟩

private theorem idealBound_eq_exp_neg_idealMultiplicity {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) 𝔣 v = WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) :=
  idealBound_of_ne_bot h𝔣 v

private theorem eta_eq_one_of_mem_modulusNhd (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ modulusNhd F 𝔣)
    (harch : (↑x : AdeleRing (𝓞 F) F).1 = 1) : η x = 1 := by
  obtain ⟨hint, hintinv, hcong⟩ := hx
  refine hmod x harch (fun v => ⟨?_, ?_⟩)
  ·
    have hle : Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) ≤ 1 := hint v
    have hinvle : Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
      hintinv v
    have hx1 : ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
        * (↑x : AdeleRing (𝓞 F) F).2 v = 1 := by
      have h : ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
          * (↑x : AdeleRing (𝓞 F) F) = 1 := x.inv_mul
      calc ((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
            * (↑x : AdeleRing (𝓞 F) F).2 v
          = (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
              * (↑x : AdeleRing (𝓞 F) F)).2 v := rfl
        _ = (1 : AdeleRing (𝓞 F) F).2 v := by rw [h]
        _ = 1 := rfl
    refine le_antisymm hle ?_
    have hprod : Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
        * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, hx1, map_one]
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (((↑x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
            * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) := hprod.symm
      _ ≤ 1 * Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) :=
          mul_le_mul_left hinvle _
      _ = Valued.v ((↑x : AdeleRing (𝓞 F) F).2 v) := one_mul _
  ·
    have hcv := hcong v
    rw [coe_sub_apply, coe_one_apply] at hcv
    exact hcv.trans_eq (idealBound_eq_exp_neg_idealMultiplicity F h𝔣 v)

private theorem arch_det_eq_one_of_mem_finiteAdelic
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    (↑(Matrix.GeneralLinearGroup.det u) : AdeleRing (𝓞 F) F).1 = 1 := by
  have hmap := Matrix.GeneralLinearGroup.map_det (f := adeleArch (𝓞 F) F) u
  rw [show Matrix.GeneralLinearGroup.map (adeleArch (𝓞 F) F) = glArch (𝓞 F) F from rfl,
    (mem_finiteAdelicGL2Subgroup_iff F u).mp hu, map_one] at hmap
  exact congrArg Units.val hmap.symm

private theorem isKfSmooth_chiDet_of_admitsModulus (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    IsKfSmooth F (chiDet (𝓞 F) F η) := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(η.comp Matrix.GeneralLinearGroup.det).ker.comap (finiteAdelicGL2Subgroup F).subtype,
    ?_, fun u hu => ?_⟩
  ·
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset
        (((isOpen_modulusNhd F 𝔣 h𝔣).preimage
          (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)).mem_nhds ?_)
        (fun u hu => ?_))
    · show Matrix.GeneralLinearGroup.det ((1 : finiteAdelicGL2Subgroup F) : AdelicGL2 (𝓞 F) F)
        ∈ modulusNhd F 𝔣
      rw [show ((1 : finiteAdelicGL2Subgroup F) : AdelicGL2 (𝓞 F) F) = 1 from rfl, map_one]
      exact one_mem_modulusNhd F 𝔣
    ·
      exact eta_eq_one_of_mem_modulusNhd F η h𝔣 hmod hu
        (arch_det_eq_one_of_mem_finiteAdelic F u.2)
  ·
    refine FLT.SmoothVectors.RightTranslationFn.ext fun g => ?_
    rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]
    show chiDet (𝓞 F) F η (g * (u : AdelicGL2 (𝓞 F) F)) = chiDet (𝓞 F) F η g
    have hu' : η (Matrix.GeneralLinearGroup.det (u : AdelicGL2 (𝓞 F) F)) = 1 :=
      Subgroup.mem_comap.mp hu
    unfold chiDet
    rw [map_mul, map_mul, hu', mul_one]

private theorem isLsXiFunction_gaussSumFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) :
    IsLsXiFunction (𝓞 F) F Z ξ (gaussSumFn F η 𝔣 φ) where
  left_invariant γ g := by
    unfold gaussSumFn
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_assoc, hφ.left_invariant γ (g * gaussTrans F 𝔣 u)]
  central_transform z g := by
    unfold gaussSumFn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_assoc, hφ.central_transform z (g * gaussTrans F 𝔣 u)]
    ring

private theorem isCuspidalFn_gaussSumFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    {nS : MeasurableSpace (AdeleRing (𝓞 F) F)} (ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hint : ∀ g, MeasureTheory.Integrable (constantTermIntegrand unipotentGL2 φ g) ν)
    (hφ : @IsCuspidalFn _ nS _ _ ν unipotentGL2 φ) :
    @IsCuspidalFn _ nS _ _ ν unipotentGL2 (gaussSumFn F η 𝔣 φ) := by
  intro g
  unfold constantTerm constantTermIntegrand gaussSumFn
  calc ∫ q, ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u
          * φ (unipotentGL2 q * g * gaussTrans F 𝔣 u) ∂ν
      = ∫ q, ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u
          * φ (unipotentGL2 q * (g * gaussTrans F 𝔣 u)) ∂ν :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q =>
          Finset.sum_congr rfl fun u _ => by rw [mul_assoc])
    _ = ∑ u : GaussIndex F 𝔣, ∫ q, gaussWt F η 𝔣 u
          * φ (unipotentGL2 q * (g * gaussTrans F 𝔣 u)) ∂ν :=
        MeasureTheory.integral_finsetSum _
          (fun u _ => (hint (g * gaussTrans F 𝔣 u)).const_mul (gaussWt F η 𝔣 u))
    _ = 0 := by
        refine Finset.sum_eq_zero fun u _ => ?_
        rw [MeasureTheory.integral_const_mul,
          show (∫ q, φ (unipotentGL2 q * (g * gaussTrans F 𝔣 u)) ∂ν)
            = constantTerm ν unipotentGL2 φ (g * gaussTrans F 𝔣 u) from rfl,
          hφ (g * gaussTrans F 𝔣 u), mul_zero]

private theorem isKfSmooth_gaussSumFn (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    IsKfSmooth F (gaussSumFn F η 𝔣 φ) := by
  rw [isKfSmooth_iff] at hφ ⊢
  have hterm : ∀ u : GaussIndex F 𝔣, FLT.SmoothVectors.IsSmoothVector
      (finiteAdelicGL2Subgroup F)
      (FLT.SmoothVectors.RightTranslationFn.mk (G := AdelicGL2 (𝓞 F) F)
        (fun g => gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u))) := by
    intro u
    have hmem : gaussTrans F 𝔣 u ∈ finiteAdelicGL2Subgroup F :=
      (mem_finiteAdelicGL2Subgroup_iff F _).mpr (by
        unfold gaussTrans
        exact P7LevelMono.glArch_finLift _)
    have hsm := FLT.SmoothVectors.IsSmoothVector.smul hφ (⟨gaussTrans F 𝔣 u, hmem⟩ :
      finiteAdelicGL2Subgroup F)
    have heq : ((⟨gaussTrans F 𝔣 u, hmem⟩ : finiteAdelicGL2Subgroup F) •
          FLT.SmoothVectors.RightTranslationFn.mk (G := AdelicGL2 (𝓞 F) F) φ)
        = FLT.SmoothVectors.RightTranslationFn.mk (G := AdelicGL2 (𝓞 F) F)
            (fun g => φ (g * gaussTrans F 𝔣 u)) :=
      FLT.SmoothVectors.RightTranslationFn.ext fun g => by
        rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]; rfl
    rw [heq] at hsm
    exact isSmoothVector_rightTranslationFn_mul (isKfSmooth_const F (gaussWt F η 𝔣 u)) hsm
  have hsumeq : (FLT.SmoothVectors.RightTranslationFn.mk
          (fun g => ∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u))
        : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)
      = ∑ u : GaussIndex F 𝔣, FLT.SmoothVectors.RightTranslationFn.mk
          (fun g => gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u)) :=
    FLT.SmoothVectors.RightTranslationFn.ext fun g => by
      show (∑ u : GaussIndex F 𝔣, gaussWt F η 𝔣 u * φ (g * gaussTrans F 𝔣 u))
        = FLT.SmoothVectors.RightTranslationFn.toFun (∑ u : GaussIndex F 𝔣,
            FLT.SmoothVectors.RightTranslationFn.mk
              (fun g' => gaussWt F η 𝔣 u * φ (g' * gaussTrans F 𝔣 u))) g
      unfold FLT.SmoothVectors.RightTranslationFn.toFun FLT.SmoothVectors.RightTranslationFn.mk
      exact (Finset.sum_apply g Finset.univ
        (fun u g' => gaussWt F η 𝔣 u * φ (g' * gaussTrans F 𝔣 u))).symm
  unfold gaussSumFn
  rw [hsumeq]
  exact Finset.sum_induction _
    (fun f => FLT.SmoothVectors.IsSmoothVector (finiteAdelicGL2Subgroup F) f)
    (fun _ _ => FLT.SmoothVectors.IsSmoothVector.add)
    FLT.SmoothVectors.isSmoothVector_zero (fun u _ => hterm u)

private theorem gaussSumFn_centralScalar_mul (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {b : ℂ} (z : (AdeleRing (𝓞 F) F)ˣ)
    (hφ : ∀ g, φ (centralScalar (𝓞 F) F z * g) = b * φ g) (g : AdelicGL2 (𝓞 F) F) :
    gaussSumFn F η 𝔣 φ (centralScalar (𝓞 F) F z * g) = b * gaussSumFn F η 𝔣 φ g := by
  unfold gaussSumFn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mul_assoc, hφ (g * gaussTrans F 𝔣 u)]; ring

end P7RamTwist

section Prints
end Prints

end
end M4aP7_RamifiedTwist

private theorem whittakerCoefficient_comb_aux (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ)
    {ι : Type} [Fintype ι] (w : ι → ℂ)
    (n : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)
    (h3 : ∀ (α : F) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      AutomorphicForm.WhittakerCoefficientIntegrable F pins ψ φ α g)
    (α : F) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    AutomorphicForm.whittakerCoefficient F pins ψ (fun x => ∑ v : ι, w v * φ (x * n v)) α g =
      ∑ v : ι, w v * AutomorphicForm.whittakerCoefficient F pins ψ φ α (g * n v) := by
  simp only [AutomorphicForm.WhittakerCoefficientIntegrable] at h3
  simp only [AutomorphicForm.whittakerCoefficient]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum _ fun v _ => (h3 α (g * n v)).const_mul _]
  simp_rw [MeasureTheory.integral_const_mul]

private theorem isBoundedGenuineFn_comb_aux (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ)
    {ι : Type} [Fintype ι] (w : ι → ℂ)
    (n : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)
    (h : AutomorphicForm.IsBoundedGenuineFn F pins ψ φ) :
    AutomorphicForm.IsBoundedGenuineFn F pins ψ (fun x => ∑ v : ι, w v * φ (x * n v)) := by
  classical
  rw [AutomorphicForm.isBoundedGenuineFn_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact continuous_finsetSum _ fun v _ =>
      continuous_const.mul (h1.comp (continuous_id.mul continuous_const))
  ·
    intro c u d₁ d₂ T hc hd₁
    choose C hC using fun v : ι => h2 c u d₁ d₂ (T.image (· * n v)) hc hd₁
    refine ⟨∑ v : ι, ‖w v‖ * C v, ?_⟩
    intro g hg
    obtain ⟨x, hxT, s, hs, rfl⟩ := Set.mem_iUnion₂.1 hg
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hC v _ ?_) (norm_nonneg _)
    exact Set.mem_iUnion₂.2
      ⟨x * n v, Finset.mem_image_of_mem (· * n v) hxT, ⟨s, hs, (mul_assoc s x (n v)).symm⟩⟩
  ·
    intro α g
    simp only [AutomorphicForm.WhittakerCoefficientIntegrable] at h3 ⊢
    simp_rw [Finset.sum_mul, mul_assoc]
    exact MeasureTheory.integrable_finsetSum _ fun v _ => (h3 α (g * n v)).const_mul _
  ·
    intro g
    simp_rw [whittakerCoefficient_comb_aux F pins ψ w n φ h3]
    exact summable_sum fun v _ => (h4 (g * n v)).mul_left _

theorem solution
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηF : IsIdeleClassChar (𝓞 F) F η) (hcont : Continuous η)
    (hη₁ : IsUnitaryChar (𝓞 F) F η)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {nS : MeasurableSpace (AdeleRing (𝓞 F) F)} (ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F))
    {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ)
    (hint : ∀ g, MeasureTheory.Integrable (constantTermIntegrand unipotentGL2 φ g) ν)
    (hcusp : @IsCuspidalFn _ nS _ _ ν unipotentGL2 φ)
    (hkf : IsKfSmooth F φ)
    (hgen : IsBoundedGenuineFn F pins ψ φ) :
    Continuous (chiDet (𝓞 F) F η) ∧
      IsLsXiFunction (𝓞 F) F Z (twistedCentralChar F Z ξ η)
        (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) ∧
      (@IsCuspidalFn _ nS _ _ ν unipotentGL2
        (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ))) ∧
      IsKfSmooth F (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) ∧
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (b : ℂ),
        (∀ g : AdelicGL2 (𝓞 F) F, φ (centralScalar (𝓞 F) F z * g) = b * φ g) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) (centralScalar (𝓞 F) F z * g)
            = ((η z : ℂˣ) : ℂ) ^ 2 * b *
                fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) g) ∧
      IsBoundedGenuineFn F pins ψ (fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P7RamTwist.continuous_chiDet_of_continuous F η hcont
  · exact isLsXiFunction_fnTwist F η hηF (P7RamTwist.isLsXiFunction_gaussSumFn F η 𝔣 hφ)
  · exact AutomorphicForm.TwistRealization.isCuspidalFn_fnTwist η ν
      (P7RamTwist.isCuspidalFn_gaussSumFn F η 𝔣 ν hint hcusp)
  · exact isKfSmooth_fnTwist F η (P7RamTwist.isKfSmooth_chiDet_of_admitsModulus F η 𝔣 h𝔣 hmod)
      (P7RamTwist.isKfSmooth_gaussSumFn F η 𝔣 hkf)
  · intro z b hb g
    change P7RamTwist.gaussTwistFn F η 𝔣 φ (centralScalar (𝓞 F) F z * g)
      = ((η z : ℂˣ) : ℂ) ^ 2 * b * P7RamTwist.gaussTwistFn F η 𝔣 φ g
    rw [P7RamTwist.gaussTwistFn, fnTwist_apply, fnTwist_apply, chiDet_centralScalar_mul,
      P7RamTwist.gaussSumFn_centralScalar_mul F η 𝔣 z hb g]
    ring
  · exact (isBoundedGenuineFn_comb_aux F pins ψ (AutomorphicForm.GaussTwist.gaussWt F η 𝔣)
      (AutomorphicForm.GaussTwist.gaussTrans F 𝔣) φ hgen).detTwist (fun x => ((η x : ℂˣ) : ℂ))
      (P7RamTwist.continuous_chiDet_of_continuous F η hcont) (fun u => (hη₁ u).le)

end S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData
end P2MW
export P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_isSmoothCuspData (solution)
