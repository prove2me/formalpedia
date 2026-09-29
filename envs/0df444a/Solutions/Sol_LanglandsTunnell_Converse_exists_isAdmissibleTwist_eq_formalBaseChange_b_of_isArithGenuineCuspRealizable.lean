-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isAdmissibleTwist_eq_formalBaseChange_b_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5f194c93-d14e-5a45-b664-3d6b08fc1ea5

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_M4aHerbrand_GenuineTensorEquiv
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_DedekindDomain_IntegralClosure
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_ProductionNotionGateEigensystems
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open NumberField.TateGlobal

noncomputable section

section Det

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGenAt (v : HeightOneSpectrum R) (t : (v.adicCompletion K)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt R K v t)
      = Units.map (finIncl R K) (localUnit R K v t) :=
  det_diagOne _

private theorem det_heckeGen (v : HeightOneSpectrum R) :
    Matrix.GeneralLinearGroup.det (heckeGen R K v)
      = Units.map (finIncl R K) (localUnit R K v (uniformizerUnit K v)) :=
  det_heckeGenAt v _

end Det

section NumberField

variable {F : Type} [Field F] [NumberField F]

private theorem det_heckeGen_eq_uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v :=
  det_heckeGen v

private theorem fst_finIncl_localUnit (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rw [Units.coe_map]
  exact finIncl_apply_fst (𝓞 F) F _

private theorem snd_finIncl_localUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :
      FiniteAdeleRing (𝓞 F) F) v = (t : v.adicCompletion F) := by
  rw [Units.coe_map]
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = t
  exact localUnit_apply_self (𝓞 F) F v t

private theorem snd_finIncl_localUnit_of_ne (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :
      FiniteAdeleRing (𝓞 F) F) w = 1 := by
  rw [Units.coe_map]
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1
  exact localUnit_apply_of_ne (𝓞 F) F v t hw

private theorem valued_eq_one_of_mem_integers {v : HeightOneSpectrum (𝓞 F)} (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Valued.v (t : v.adicCompletion F) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ht'
  rw [Units.val_inv_eq_inv_val, Valuation.map_inv] at ht'
  have hne : Valued.v (t : v.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr t.ne_zero
  exact le_antisymm ht ((inv_le_one₀ (lt_of_le_of_ne (zero_le' ) hne.symm)).mp ht')

private theorem isUnramifiedCharAt_of_admitsModulus {θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 F)}
    (hθ : HeckeCharacter.AdmitsModulus F θ 𝔣) {v : HeightOneSpectrum (𝓞 F)}
    (hv : HeckeCharacter.idealMultiplicity F v 𝔣 = 0) :
    IsUnramifiedCharAt θ v := by
  intro t ht ht'
  rw [localChar_apply]
  refine hθ _ (fst_finIncl_localUnit v t) fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [snd_finIncl_localUnit_self _ t, hv]
    refine ⟨valued_eq_one_of_mem_integers t ht ht', ?_⟩
    simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valued.v.map_sub_le (le_of_eq (valued_eq_one_of_mem_integers t ht ht')) (le_of_eq Valued.v.map_one)
  · rw [snd_finIncl_localUnit_of_ne v t hw]
    refine ⟨Valued.v.map_one, ?_⟩
    rw [sub_self, Valued.v.map_zero]
    exact zero_le'

end NumberField

section Interface

private theorem omegaSup_det_heckeGen (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v :=
  det_heckeGen_eq_uniformizerIdele v

private theorem omegaSup_mem_integers_and_inv_mem_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) ↔
      Valued.v (t : v.adicCompletion F) = 1 := by
  constructor
  · rintro ⟨ht, ht'⟩
    exact valued_eq_one_of_mem_integers t ht ht'
  · intro h
    refine ⟨?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, Valuation.map_inv, h,
        inv_one]

private theorem omegaSup_isUnramifiedCharAt_of_admitsModulus (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (h : HeckeCharacter.AdmitsModulus F χ 𝔣)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔣) : IsUnramifiedCharAt χ v := by
  refine isUnramifiedCharAt_of_admitsModulus h ?_
  by_contra hne
  rcases eq_or_ne 𝔣 ⊥ with rfl | h𝔣
  · exact hv (dvd_zero _)
  · exact hv ((Associates.count_ne_zero_iff_dvd (show 𝔣 ≠ 0 from h𝔣) v.irreducible).mp hne)

end Interface

end

open scoped TensorProduct
open M4aHerbrand M4aHerbrand.GenuineDescent M4aHerbrand.Bridge

noncomputable section

private theorem continuous_norm_of_basis
    (A B : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra A B] [TopologicalSpace B] [IsModuleTopology A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) :
    Continuous (fun x : B => Algebra.norm A x) := by
  classical
  have h : (fun x : B => Algebra.norm A x) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext fun x => Algebra.norm_eq_matrix_det b x
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  have h2 : (fun x : B => Algebra.leftMulMatrix b x i j) = fun x => b.repr (x * b j) i :=
    funext fun x => Algebra.leftMulMatrix_eq_repr_mul b x i j
  rw [h2]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight A (b j)))

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private scoped instance moduleFinite_of_numberFields : Module.Finite K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

private theorem isModuleTopology_genuine :
    letI := (genuineβ K L).toAlgebra
    IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := by
  letI := (genuineβ K L).toAlgebra
  exact isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L (continuous_genuineβ K L)
    (genuineTensorEquiv K L)

private def genuineBasis :
    letI := (genuineβ K L).toAlgebra
    Module.Basis (Module.Free.ChooseBasisIndex K L) (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  letI := (genuineβ K L).toAlgebra
  ((Module.Free.chooseBasis K L).baseChange (AdeleRing (𝓞 K) K)).map
    (genuineTensorEquiv K L).toLinearEquiv

private theorem continuous_genuineAdelicNorm :
    Continuous ((genuineBaseChange K L).adelicNorm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 K) K) := by
  letI := (genuineβ K L).toAlgebra
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := isModuleTopology_genuine K L
  show Continuous (fun x : AdeleRing (𝓞 L) L => Algebra.norm (AdeleRing (𝓞 K) K) x)
  exact continuous_norm_of_basis (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (genuineBasis K L)

private theorem continuous_genuineIdelicNorm :
    Continuous ((genuineBaseChange K L).idelicNorm :
      (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ) :=
  Continuous.units_map (genuineBaseChange K L).adelicNorm (continuous_genuineAdelicNorm K L)

omit [NumberField L] in

private theorem lmul_one_tmul (α : L) :
    Algebra.lmul (AdeleRing (𝓞 K) K) ((AdeleRing (𝓞 K) K) ⊗[K] L) ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] α)
      = (Algebra.lmul K L α).baseChange (AdeleRing (𝓞 K) K) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem adelicNorm_algebraMap (α : L) :
    (genuineBaseChange K L).adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) α)
      = algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K α) := by
  letI := (genuineβ K L).toAlgebra
  have h1 : algebraMap L (AdeleRing (𝓞 L) L) α
      = genuineTensorEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] α) :=
    (genuineTensorEquiv_one_tmul K L α).symm
  show Algebra.norm (AdeleRing (𝓞 K) K) (algebraMap L (AdeleRing (𝓞 L) L) α) = _
  rw [h1, Algebra.norm_eq_of_algEquiv, Algebra.norm_apply (R := AdeleRing (𝓞 K) K), lmul_one_tmul,
    LinearMap.det_baseChange, Algebra.norm_apply (R := K)]

private theorem idelicNorm_principal (α : Lˣ) :
    (genuineBaseChange K L).idelicNorm
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) α)
      = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (Units.map (Algebra.norm K : L →* K) α) := by
  apply Units.ext
  show (genuineBaseChange K L).adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) (α : L))
    = algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K (α : L))
  exact adelicNorm_algebraMap K L α

variable {K L}

private theorem ext_val_injective {v : HeightOneSpectrum (𝓞 K)} {w w' : v.Extension (𝓞 L)}
    (h : w'.1 = w.1) : w' = w :=
  Subtype.ext h

private theorem ext_val_ne_of_ne {u v : HeightOneSpectrum (𝓞 K)} (huv : u ≠ v)
    (w' : u.Extension (𝓞 L)) (w : v.Extension (𝓞 L)) : w'.1 ≠ w.1 := by
  intro h
  apply huv
  rw [← w'.2, ← w.2, h]

variable (K L)

private theorem idelicNorm_finIncl_localUnit (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (t : (w.1.adicCompletion L)ˣ) :
    (genuineBaseChange K L).idelicNorm (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w.1 t))
      = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v
          (Units.map (Algebra.norm (v.adicCompletion K) : w.1.adicCompletion L →* v.adicCompletion K)
            t)) := by
  classical
  set y : AdeleRing (𝓞 L) L :=
    finIncl (𝓞 L) L ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
  have hself : (y.2 : FiniteAdeleRing (𝓞 L) L) w.1 = (t : w.1.adicCompletion L) :=
    localUnit_apply_self (𝓞 L) L w.1 t
  have hoff : ∀ {u : HeightOneSpectrum (𝓞 L)}, u ≠ w.1 → (y.2 : FiniteAdeleRing (𝓞 L) L) u = 1 :=
    fun hu => localUnit_apply_of_ne (𝓞 L) L w.1 t hu
  have hcomp := genuineAdelicNorm_componentwise K L y
  have hN : (genuineBaseChange K L).adelicNorm y
      = (letI := (genuineβ K L).toAlgebra; Algebra.norm (AdeleRing (𝓞 K) K) y) := rfl
  apply Units.ext
  show (genuineBaseChange K L).adelicNorm y
    = finIncl (𝓞 K) K ((localUnit (𝓞 K) K v (Units.map (Algebra.norm (v.adicCompletion K)) t) :
        (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)
  rw [hN]
  refine Prod.ext ?_ ?_
  ·
    have hy1 : y.1 = 1 := rfl
    rw [finIncl_apply_fst, hcomp.1, hy1]
    exact map_one _
  ·
    rw [finIncl_apply_snd]
    apply FiniteAdeleRing.ext
    intro u
    letI : Fintype (u.Extension (𝓞 L)) :=
      IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) u
    rw [hcomp.2 u]
    by_cases huv : u = v
    · subst huv
      rw [localUnit_apply_self, Units.coe_map, Finset.prod_eq_single w]
      · rw [hself]
      · intro w' _ hw'
        have hne : w'.1 ≠ w.1 := fun h => hw' (ext_val_injective h)
        rw [hoff hne, map_one]
      · intro habs
        exact absurd (Finset.mem_univ w) habs
    · rw [localUnit_apply_of_ne (𝓞 K) K v _ huv]
      refine Finset.prod_eq_one fun w' _ => ?_
      rw [hoff (ext_val_ne_of_ne huv w' w), map_one]

private abbrev extensionOfUnder (𝔓 : HeightOneSpectrum (𝓞 L)) : (𝔓.under (𝓞 K)).Extension (𝓞 L) :=
  Subtype.mk 𝔓 rfl

end

section Interface

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem omegaSup_continuous_idelicNorm : Continuous (genuineBaseChange K L).idelicNorm :=
  continuous_genuineIdelicNorm K L

private theorem omegaSup_idelicNorm_principal (α : Lˣ) :
    (genuineBaseChange K L).idelicNorm (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α) :=
  idelicNorm_principal K L α

private theorem omegaSup_idelicNorm_localUnit (𝔓 : HeightOneSpectrum (𝓞 L)) (y : (𝔓.adicCompletion L)ˣ) :
    ∃ s : ((𝔓.under (𝓞 K)).adicCompletion K)ˣ,
      Valued.v (s : (𝔓.under (𝓞 K)).adicCompletion K) =
        Valued.v (y : 𝔓.adicCompletion L) ^ Ideal.inertiaDeg' (𝔓.under (𝓞 K)).asIdeal 𝔓.asIdeal ∧
      (genuineBaseChange K L).idelicNorm (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L 𝔓 y)) =
        Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (𝔓.under (𝓞 K)) s) := by
  refine ⟨_, ?_, idelicNorm_finIncl_localUnit K L (𝔓.under (𝓞 K)) (extensionOfUnder K L 𝔓) y⟩
  exact valuation_norm_adicCompletion_eq_pow_inertiaDeg K L (𝔓.under (𝓞 K)) (extensionOfUnder K L 𝔓)
    (y : 𝔓.adicCompletion L)

end Interface

open LanglandsTunnell.Converse

noncomputable section

private theorem omegaSup_subsingleton_algebra_ratInt (S : Type*) [Semiring S] :
    Subsingleton (Algebra (𝓞 ℚ) S) := by
  have key : ∀ f g : 𝓞 ℚ →+* S, f = g := fun f g => by
    have hfg : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom =
        g.comp Rat.ringOfIntegersEquiv.symm.toRingHom := Subsingleton.elim _ _
    refine RingHom.ext fun x => ?_
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact RingHom.congr_fun hfg n
  exact ⟨fun P Q => Algebra.algebra_ext P Q fun r => RingHom.congr_fun (key _ _) r⟩

private def omegaSup_modulusChar (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((ideleNorm F x : ℝ) : ℂ) (by exact_mod_cast (ideleNorm_pos x).ne')
  map_one' := Units.ext (by rw [Units.val_mk0, ideleNorm_one, Complex.ofReal_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul, Complex.ofReal_mul])

private theorem omegaSup_coe_modulusChar_apply (F : Type) [Field F] [NumberField F] (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((omegaSup_modulusChar F x : ℂˣ) : ℂ) = ((ideleNorm F x : ℝ) : ℂ) := rfl

private theorem omegaSup_continuous_modulusChar (F : Type) [Field F] [NumberField F] :
    Continuous (omegaSup_modulusChar F) := by
  have hc : Continuous (ideleNorm F) := NumberField.TateGlobal.continuous_ideleNorm F
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Complex.continuous_ofReal.comp hc
  · have h2 : Continuous fun x => ((ideleNorm F x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hc
    have : (fun x => ((omegaSup_modulusChar F x)⁻¹ : ℂˣ).val) = fun x => (((ideleNorm F x : ℝ) : ℂ))⁻¹ := by
      funext x; rw [Units.val_inv_eq_inv_val]; rfl
    rw [this]
    exact h2.inv₀ fun x => Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne'

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ)) :
    ∃ Tq : Finset (HeightOneSpectrum (𝓞 ℚ)), ∃ ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsAdmissibleTwist K ω ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
        IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓 := by
  have _ := ha
  classical

  haveI := omegaSup_subsingleton_algebra_ratInt (𝓞 K)
  obtain ⟨⟩ : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _

  obtain ⟨R, hR⟩ := hΦ

  obtain ⟨hcls, hmod, hcont⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      ℚ _ _ _ _ R

  have hval : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ R.exceptionalSet →
      (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (uniformizerIdele ℚ p) : ℂˣ) : ℂ) =
        (HeckeEigensystem.cNorm p)⁻¹ * Φ.b p := fun p hp => by
    have hz : ((Subgroup.topEquiv.symm (uniformizerIdele ℚ p) : (productionPinsGeneral ℚ).Z) :
        (AdeleRing (𝓞 ℚ) ℚ)ˣ) = Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen p) := by
      show uniformizerIdele ℚ p = Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ p)
      exact (omegaSup_det_heckeGen ℚ p).symm
    have h1 := R.centralChar_det_gen_eq_b hp _ hz
    exact h1

  obtain ⟨ξ', hcls, hξc, hmod, hval⟩ : ∃ ξ' : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      IsIdeleClassChar (𝓞 ℚ) ℚ ξ' ∧ Continuous ξ' ∧ HeckeCharacter.AdmitsModulus ℚ ξ' Φ.level ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ R.exceptionalSet →
          ((ξ' (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = (HeckeEigensystem.cNorm p)⁻¹ * Φ.b p :=
    ⟨_, hcls, hcont hR, hmod, hval⟩

  obtain ⟨σ, hσ⟩ := RatIdele.exists_norm_apply_eq_ideleNorm_rpow ξ' hcls hξc
  haveI := AutomorphicForm.infinite_heightOneSpectrum_ratO
  obtain ⟨p₀, hp₀⟩ := Infinite.exists_notMem_finset (SQ₀ ∪ R.exceptionalSet)
  have hp₀S : p₀ ∉ SQ₀ := fun h => hp₀ (Finset.mem_union_left _ h)
  have hp₀E : p₀ ∉ R.exceptionalSet := fun h => hp₀ (Finset.mem_union_right _ h)
  have hNgt : (1 : ℝ) < ((Ideal.absNorm p₀.asIdeal : ℕ) : ℝ) := by
    have h0 : Ideal.absNorm p₀.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p₀.ne_bot
    have h1 : Ideal.absNorm p₀.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr p₀.isPrime.ne_top
    exact_mod_cast (show 1 < Ideal.absNorm p₀.asIdeal by omega)
  have hσ1 : σ = 1 := by
    have h := hσ (uniformizerIdele ℚ p₀)
    have hc : ‖HeckeEigensystem.cNorm p₀‖ = ((Ideal.absNorm p₀.asIdeal : ℕ) : ℝ) := by
      unfold HeckeEigensystem.cNorm
      exact Complex.norm_natCast _
    rw [hval p₀ hp₀E, NumberField.TateGlobal.ideleNorm_uniformizerIdele ℚ p₀, norm_mul, norm_inv, hc,
      hb p₀ hp₀S, mul_one] at h
    set a : ℝ := ((Ideal.absNorm p₀.asIdeal : ℕ) : ℝ)⁻¹ with ha
    have ha0 : 0 < a := inv_pos.mpr (lt_trans one_pos hNgt)
    have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hNgt
    have h' : a ^ σ = a ^ (1 : ℝ) := by rw [Real.rpow_one]; exact h.symm
    rcases lt_trichotomy σ 1 with hlt | heq | hgt
    · exact absurd h' (ne_of_gt ((Real.rpow_lt_rpow_left_iff_of_base_lt_one ha0 ha1).mpr hlt))
    · exact heq
    · exact absurd h'.symm (ne_of_gt ((Real.rpow_lt_rpow_left_iff_of_base_lt_one ha0 ha1).mpr hgt))
  subst hσ1
  have hnormξ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((ξ' x : ℂˣ) : ℂ)‖ = ideleNorm ℚ x := fun x => by
    rw [hσ x, Real.rpow_one]
  have hnorm1 : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ξ' x = 1 → ideleNorm ℚ x = 1 := fun x hx => by
    have h := hnormξ x
    rw [hx, Units.val_one, norm_one] at h
    exact h.symm

  have hχapply : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((((ξ' * (omegaSup_modulusChar ℚ)⁻¹) x) : ℂˣ) : ℂ) = ((ξ' x : ℂˣ) : ℂ) * (((ideleNorm ℚ x : ℝ) : ℂ))⁻¹ :=
    fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      omegaSup_coe_modulusChar_apply]
  have hχu : IsUnitaryChar (𝓞 ℚ) ℚ (ξ' * (omegaSup_modulusChar ℚ)⁻¹) := fun x => by
    rw [hχapply x, norm_mul, norm_inv, hnormξ x, Complex.norm_of_nonneg (ideleNorm_pos x).le,
      mul_inv_cancel₀ (ideleNorm_pos x).ne']
  have hχcls : IsIdeleClassChar (𝓞 ℚ) ℚ (ξ' * (omegaSup_modulusChar ℚ)⁻¹) := fun u => by
    apply Units.ext
    rw [hχapply, hcls u, hnorm1 _ (hcls u), Units.val_one, one_mul, Complex.ofReal_one, inv_one]
  have hχc : Continuous (ξ' * (omegaSup_modulusChar ℚ)⁻¹) := by
    have h : Continuous fun x => ξ' x * ((omegaSup_modulusChar ℚ) x)⁻¹ :=
      hξc.mul (omegaSup_continuous_modulusChar ℚ).inv
    refine h.congr fun x => ?_
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
  have hχunr : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ p.asIdeal ∣ Φ.level →
      IsUnramifiedCharAt (ξ' * (omegaSup_modulusChar ℚ)⁻¹) p := fun p hp t ht hti => by
    have h1 := omegaSup_isUnramifiedCharAt_of_admitsModulus ℚ ξ' Φ.level hmod p hp t ht hti
    rw [NumberField.TateGlobal.localChar_apply] at h1
    apply Units.ext
    rw [NumberField.TateGlobal.localChar_apply, hχapply, h1, hnorm1 _ h1, Units.val_one, one_mul,
      Complex.ofReal_one, inv_one]
  have hχval : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ R.exceptionalSet →
      ((((ξ' * (omegaSup_modulusChar ℚ)⁻¹) (uniformizerIdele ℚ p)) : ℂˣ) : ℂ) = Φ.b p := fun p hp => by
    have hN0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
    rw [hχapply, hval p hp, NumberField.TateGlobal.ideleNorm_uniformizerIdele ℚ p, Complex.ofReal_inv,
      Complex.ofReal_natCast, inv_inv]
    unfold HeckeEigensystem.cNorm
    rw [mul_comm ((Ideal.absNorm p.asIdeal : ℂ))⁻¹ (Φ.b p), mul_assoc, inv_mul_cancel₀ hN0, mul_one]

  obtain ⟨χ, hχu, hχcls, hχc, hχunr, hχval⟩ : ∃ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      IsUnitaryChar (𝓞 ℚ) ℚ χ ∧ IsIdeleClassChar (𝓞 ℚ) ℚ χ ∧ Continuous χ ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ p.asIdeal ∣ Φ.level → IsUnramifiedCharAt χ p) ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ R.exceptionalSet →
          ((χ (uniformizerIdele ℚ p) : ℂˣ) : ℂ) = Φ.b p :=
    ⟨_, hχu, hχcls, hχc, hχunr, hχval⟩

  refine ⟨R.exceptionalSet ∪ (Ideal.finite_factors Φ.level_ne_bot).toFinset,
    χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm,
    And.intro ?_ (And.intro ?_ ?_), ?_⟩
  ·
    intro u
    rw [MonoidHom.comp_apply, omegaSup_idelicNorm_principal ℚ K u]
    exact hχcls _
  ·
    exact hχc.comp (omegaSup_continuous_idelicNorm ℚ K)
  ·
    intro x
    exact hχu _
  · intro 𝔓 h𝔓
    have hpE : 𝔓.under (𝓞 ℚ) ∉ R.exceptionalSet := fun h => h𝔓 (Finset.mem_union_left _ h)
    have hpL : ¬ (𝔓.under (𝓞 ℚ)).asIdeal ∣ Φ.level := fun h =>
      h𝔓 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    have hunr := hχunr (𝔓.under (𝓞 ℚ)) hpL
    refine ⟨?_, ?_⟩
    ·
      intro t ht hti
      have hvt : Valued.v (t : 𝔓.adicCompletion K) = 1 :=
        (omegaSup_mem_integers_and_inv_mem_iff K 𝔓 t).mp ⟨ht, hti⟩
      obtain ⟨s, hs, hNs⟩ := omegaSup_idelicNorm_localUnit ℚ K 𝔓 t
      rw [hvt, one_pow] at hs
      obtain ⟨hs1, hs2⟩ := (omegaSup_mem_integers_and_inv_mem_iff ℚ (𝔓.under (𝓞 ℚ)) s).mpr hs
      rw [NumberField.TateGlobal.localChar_apply, MonoidHom.comp_apply, hNs]
      have h := hunr s hs1 hs2
      rwa [NumberField.TateGlobal.localChar_apply] at h
    ·
      obtain ⟨s, hs, hNs⟩ := omegaSup_idelicNorm_localUnit ℚ K 𝔓 (uniformizerUnit K 𝔓)
      rw [valued_uniformizerUnit] at hs
      have huni : uniformizerIdele K 𝔓 =
          Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K 𝔓 (uniformizerUnit K 𝔓)) := rfl
      rw [huni, MonoidHom.comp_apply, hNs]
      have hsu : s = uniformizerUnit ℚ (𝔓.under (𝓞 ℚ)) ^ Ideal.inertiaDeg' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal *
          ((uniformizerUnit ℚ (𝔓.under (𝓞 ℚ)) ^ Ideal.inertiaDeg' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal)⁻¹ * s) :=
        (mul_inv_cancel_left _ _).symm
      have hvu : Valued.v (((uniformizerUnit ℚ (𝔓.under (𝓞 ℚ)) ^
            Ideal.inertiaDeg' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal)⁻¹ * s :
              ((𝔓.under (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ) = 1 := by
        rw [Units.val_mul, map_mul, hs, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
          valued_uniformizerUnit, inv_mul_cancel₀]
        exact pow_ne_zero _ WithZero.exp_ne_zero
      obtain ⟨hu1, hu2⟩ := (omegaSup_mem_integers_and_inv_mem_iff ℚ (𝔓.under (𝓞 ℚ)) _).mpr hvu
      have hχu1 := hunr _ hu1 hu2

      rw [← NumberField.TateGlobal.localChar_apply, hsu, map_mul, map_pow, hχu1, mul_one, Units.val_pow_eq_pow_val,
        NumberField.TateGlobal.localChar_apply]
      have hϖ : Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ))
          (uniformizerUnit ℚ (𝔓.under (𝓞 ℚ)))) = uniformizerIdele ℚ (𝔓.under (𝓞 ℚ)) := rfl
      rw [hϖ, hχval _ hpE, formalBaseChange_b]

end

end S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_of_isArithGenuineCuspRealizable (solution)
