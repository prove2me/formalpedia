-- Prove2me | solution 1 for M4aHerbrand.idelicNorm_levelCongr_and_realPos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d0f70fd4-5dec-5178-b2c6-49c6f40d2c32

import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_IntegralClosure
import Theorems.Thm_M4aHerbrand_adeleBaseChange_local_rigidity
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4800000

open NumberField IsDedekindDomain M4aHerbrand
open scoped TensorProduct

noncomputable section

namespace AdelicNormLevelDescent

open Module

private theorem norm_transport {ι R S R' S' : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S'] [Algebra R' S']
    (bS : Module.Basis ι R S) (c : Module.Basis ι R' S') (π : R →+* R') (P : S →+* S')
    (hP : ∀ (r : R) (s : S), P (r • s) = π r • P s) (hb : ∀ i, P (bS i) = c i) (x : S) :
    π (Algebra.norm R x) = Algebra.norm R' (P x) := by
  rw [Algebra.norm_eq_matrix_det bS, Algebra.norm_eq_matrix_det c, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have hx : P x * c j = ∑ k, π (bS.repr (x * bS j) k) • c k := by
    rw [← hb j, ← map_mul]
    conv_lhs => rw [← bS.sum_repr (x * bS j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, hb]
  rw [hx, c.repr_sum_self]

universe u v

section DetPi

variable {R : Type*} [CommRing R] {ι : Type*}
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

private def piMap (f : ∀ i, M i →ₗ[R] M i) : (∀ i, M i) →ₗ[R] (∀ i, M i) :=
  LinearMap.pi fun i => (f i).comp (LinearMap.proj i)

@[scoped simp] private theorem piMap_apply (f : ∀ i, M i →ₗ[R] M i) (x : ∀ i, M i) (i : ι) :
    piMap f x i = f i (x i) :=
  rfl

end DetPi

section DetPiInduction

variable {R : Type*} [CommRing R]

private theorem det_pi' (ι₀ : Type u) [Fintype ι₀] :
    ∀ {M : ι₀ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
      (f : ∀ i, M i →ₗ[R] M i), (piMap f).det = ∏ i, (f i).det := by
  refine Fintype.induction_empty_option
    (P := fun γ instγ =>
      ∀ {M : γ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
        [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
        (f : ∀ i, M i →ₗ[R] M i),
        (piMap f).det = (@Finset.univ γ instγ).prod fun i => (f i).det)
    ?of_equiv ?h_empty ?h_option ι₀
  case of_equiv =>
    intro α β _ e ih M _ _ _ _ f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := LinearEquiv.piCongrLeft R M e
    have hE : ∀ (y : ∀ a, M (e a)) (a), E y (e a) = y a := fun y a =>
      show Equiv.piCongrLeft M e y (e a) = y a from Equiv.piCongrLeft_apply_apply M e y a
    have hEs : ∀ (x : ∀ b, M b) (a), E.symm x a = x (e a) := fun x a =>
      show Equiv.piCongrLeft' M e.symm x a = x (e a) from rfl
    have hconj : piMap f
        = (E : (∀ a, M (e a)) →ₗ[R] ∀ b, M b) ∘ₗ (piMap fun a => f (e a))
            ∘ₗ (E.symm : (∀ b, M b) →ₗ[R] ∀ a, M (e a)) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      show f (e a) (x (e a)) = E ((piMap fun a => f (e a)) (E.symm x)) (e a)
      rw [hE]
      show f (e a) (x (e a)) = f (e a) (E.symm x a)
      rw [hEs]
    rw [hconj, LinearMap.det_conj, ih]
    exact Fintype.prod_equiv e (fun a => (f (e a)).det) (fun b => (f b).det) fun a => rfl
  case h_empty =>
    intro M _ _ _ _ f
    haveI : Subsingleton (∀ i : PEmpty, M i) := ⟨fun a b => funext fun i => i.elim⟩
    rw [LinearMap.det_eq_one_of_subsingleton, Finset.prod_of_isEmpty]
  case h_option =>
    intro α _ ih M _ _ _ _ f
    let E : (M none × ∀ a, M (some a)) ≃ₗ[R] ∀ i, M i :=
      (LinearEquiv.piOptionEquivProd R).symm
    have hconj : piMap f
        = (E : _ →ₗ[R] ∀ i, M i) ∘ₗ ((f none).prodMap (piMap fun a => f (some a)))
            ∘ₗ (E.symm : (∀ i, M i) →ₗ[R] _) := by
      apply LinearMap.ext
      intro x
      funext i
      cases i <;> rfl
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, ih, Fintype.prod_option]

end DetPiInduction

section NormPi

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
variable {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

omit [Fintype ι] in
private theorem lmul_pi (x : ∀ i, S i) :
    Algebra.lmul R (∀ i, S i) x = piMap fun i => Algebra.lmul R (S i) (x i) := by
  apply LinearMap.ext
  intro y
  rfl

private theorem norm_pi [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  rw [Algebra.norm_apply, show Algebra.lmul R (∀ i, S i) x
      = piMap fun i => Algebra.lmul R (S i) (x i) from lmul_pi x, det_pi']
  rfl

end NormPi

namespace L3

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Ov" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)
local notation "Ow" => HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)

private scoped instance charZero_adicCompletion : CharZero Kv :=
  charZero_of_injective_algebraMap (algebraMap K Kv).injective

private scoped instance isScalarTower_integers : IsScalarTower Ov Ow Lw :=
  .of_algebraMap_smul fun _ _ => rfl

private theorem algebraMap_integers_injective : Function.Injective (algebraMap Ov Ow) := by
  intro x y h
  apply Subtype.val_injective
  have h' := congrArg (fun z : Ow => (z : Lw)) h
  change (w.adicCompletionSemialgHom K L) x.val = (w.adicCompletionSemialgHom K L) y.val at h'
  exact (w.adicCompletionSemialgHom K L).toRingHom.injective h'

private scoped instance faithfulSMul_integers : FaithfulSMul Ov Ow :=
  (faithfulSMul_iff_algebraMap_injective Ov Ow).mpr (algebraMap_integers_injective K L v w)

private scoped instance isTorsionFree_integers : Module.IsTorsionFree Ov Ow := inferInstance

private scoped instance free_integers : Module.Free Ov Ow := Module.free_of_finite_type_torsion_free'

private scoped instance liesOver_completionIdeal :
    (HeightOneSpectrum.completionIdeal L w.1).LiesOver (HeightOneSpectrum.completionIdeal K v) where
  «over» := by
    rw [Ideal.under_def]
    ext x
    rw [Ideal.mem_comap, HeightOneSpectrum.mem_completionIdeal_iff, HeightOneSpectrum.mem_completionIdeal_iff,
      HeightOneSpectrum.Extension.integer_algebraMap_apply,
      HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
    exact HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
      (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1

private scoped instance perfectField_fractionRing_integers : PerfectField (FractionRing Ov) :=
  haveI : CharZero (FractionRing Ov) := charZero_of_injective_algebraMap (IsFractionRing.injective Ov _)
  inferInstance

private scoped instance isIntegralClosure_integers : IsIntegralClosure Ow Ov Lw where
  algebraMap_injective := IsFractionRing.injective Ow Lw
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top
    · rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := Ov) y).algebraMap

private theorem isLocalization_adicCompletion :
    IsLocalization (Algebra.algebraMapSubmonoid Ow (nonZeroDivisors Ov)) Lw :=
  IsIntegralClosure.isLocalization Ov Kv Lw Ow

p2m_open "NumberField.HeightOneSpectrum IsDedekindDomain.HeightOneSpectrum"

variable {K L} {v} {w}

private theorem repr_mem_of_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} (b : Module.Basis ι R M) (I : Ideal R) (x : M)
    (hx : x ∈ I • (⊤ : Submodule R M)) (i : ι) :
    b.repr x i ∈ I := by
  rw [← b.span_eq] at hx
  obtain ⟨a, ha, hax⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I b x).1 hx
  have hax' : Finsupp.linearCombination R b a = x := by
    rw [Finsupp.linearCombination_apply]; exact hax
  rw [← hax', Module.Basis.repr_linearCombination]
  exact ha i

private theorem completionIdeal_pow_le_map_pow (m : ℕ) :
    (w.1.completionIdeal L) ^ (v.asIdeal.ramificationIdx' w.1.asIdeal * m) ≤
      ((v.completionIdeal K).map (algebraMap Ov Ow)) ^ m := by
  have hbase : (w.1.completionIdeal L) ^ v.asIdeal.ramificationIdx' w.1.asIdeal ≤
      (v.completionIdeal K).map (algebraMap Ov Ow) := by
    obtain ⟨πv, hπv⟩ := adicCompletion.exists_uniformizer K v
    have hspan : (v.completionIdeal K).map (algebraMap Ov Ow) = Ideal.span {algebraMap Ov Ow πv} := by
      unfold HeightOneSpectrum.completionIdeal
      rw [adicCompletion.maximalIdeal_eq_span_uniformizer K v hπv, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    have hval : Valued.v ((algebraMap Ov Ow πv : Ow) : Lw) =
        ↑(Multiplicative.ofAdd (-(v.asIdeal.ramificationIdx' w.1.asIdeal : ℤ))) := by
      rw [Extension.integer_algebraMap_apply, Extension.valued_adicCompletionSemialgHom K L, hπv,
        ← WithZero.ofAdd_neg_ofNat_pow, w.2]
    have hval_ne : ((algebraMap Ov Ow πv : Ow) : Lw) ≠ 0 := by
      rw [← Valuation.ne_zero_iff Valued.v, hval]
      exact WithZero.coe_ne_zero
    intro z hz
    rw [adicCompletion.mem_completionIdeal_pow] at hz
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨(z : Lw) / ((algebraMap Ov Ow πv : Ow) : Lw), ?_⟩, ?_⟩
    · show Valued.v ((z : Lw) / ((algebraMap Ov Ow πv : Ow) : Lw)) ≤ 1
      rw [map_div₀, hval, div_le_one₀ (WithZero.zero_lt_coe _)]
      exact hz
    · apply Subtype.val_injective
      simp only [MulMemClass.coe_mul]
      rw [div_mul_cancel₀ _ hval_ne]
  rw [pow_mul]
  induction m with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hbase

private theorem integralNorm_sub_one_mem (I : Ideal Ov) (y₀ : Ow)
    (hy : y₀ - 1 ∈ I • (⊤ : Submodule Ov Ow)) :
    Algebra.norm Ov y₀ - 1 ∈ I := by
  classical
  let b := Module.Free.chooseBasis Ov Ow
  have hentries : ∀ i j, Algebra.leftMulMatrix b (y₀ - 1) i j ∈ I := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    refine repr_mem_of_mem_smul_top b I _ ?_ i
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hy ⊢
    exact Ideal.mul_mem_right (b j) _ hy
  have hmap : (Ideal.Quotient.mk I).mapMatrix (Algebra.leftMulMatrix b y₀) = 1 := by
    have h1 : Algebra.leftMulMatrix b y₀ = Algebra.leftMulMatrix b (y₀ - 1) + 1 := by
      rw [← map_one (Algebra.leftMulMatrix b), ← map_add]; ring_nf
    rw [h1, map_add, map_one, add_eq_right]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hentries i j)
  rw [Algebra.norm_eq_matrix_det b, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
    RingHom.map_det, hmap, Matrix.det_one, sub_self]

private theorem valued_sub_one_le_of_mem_pow {n : ℕ} (z : Ov) (hz : z - 1 ∈ (v.completionIdeal K) ^ n) :
    Valued.v ((z : Kv) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have := (adicCompletion.mem_completionIdeal_pow K v (z - 1)).1 hz
  simp at this
  exact this

private theorem mainLemma (m : ℕ) (y : Lw)
    (hy_unit : Valued.v y = 1)
    (hy_cong : Valued.v (y - 1) ≤
      WithZero.exp (-(Ideal.ramificationIdx' v.asIdeal w.1.asIdeal * m : ℤ))) :
    Valued.v (Algebra.norm Kv y) = 1 ∧
    Valued.v (Algebra.norm Kv y - 1) ≤ WithZero.exp (-(m : ℤ)) := by
  refine ⟨?_, ?_⟩
  · rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg K L v w, hy_unit, one_pow]
  ·
    have hy_mem : y ∈ (w.1.adicCompletionIntegers L) := le_of_eq hy_unit
    have h1_mem : (1 : Lw) ∈ (w.1.adicCompletionIntegers L) := one_mem _
    set y₀ : Ow := ⟨y, hy_mem⟩ with hy₀
    haveI := isLocalization_adicCompletion K L v w
    have hy₀mem : (y₀ - 1 : Ow) ∈
        (w.1.completionIdeal L) ^ (v.asIdeal.ramificationIdx' w.1.asIdeal * m) := by
      rw [adicCompletion.mem_completionIdeal_pow]
      have hcoe : ((y₀ - 1 : Ow) : Lw) = y - 1 := rfl
      rw [hcoe, show ((v.asIdeal.ramificationIdx' w.1.asIdeal * m : ℕ) : ℤ) =
          (v.asIdeal.ramificationIdx' w.1.asIdeal : ℤ) * (m : ℤ) by push_cast; ring]
      exact hy_cong
    have hy₀_smul : y₀ - 1 ∈ ((v.completionIdeal K) ^ m) • (⊤ : Submodule Ov Ow) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
      exact completionIdeal_pow_le_map_pow m hy₀mem
    have hN : Algebra.norm Ov y₀ - 1 ∈ (v.completionIdeal K) ^ m :=
      integralNorm_sub_one_mem ((v.completionIdeal K) ^ m) y₀ hy₀_smul
    have hfield : Algebra.norm Kv y = algebraMap Ov Kv (Algebra.norm Ov y₀) :=
      Algebra.norm_localization Ov (nonZeroDivisors Ov) (Rₘ := Kv) (Sₘ := Lw) y₀
    rw [hfield, show (1 : Kv) = algebraMap Ov Kv 1 from (map_one _).symm, ← map_sub]
    exact valued_sub_one_le_of_mem_pow (Algebra.norm Ov y₀) hN

end L3
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3"

section A

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def evalAt (w : HeightOneSpectrum (𝓞 L)) : FiniteAdeleRing (𝓞 L) L →+* w.adicCompletion L where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def projPi (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 L) L →+* (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  RingHom.pi fun w => (evalAt L w.1).comp (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

private theorem projPi_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    projPi K L v x w = (x.2 : FiniteAdeleRing (𝓞 L) L) w.1 := rfl

private def adeleBasis (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    letI := B.β.toAlgebra
    Module.Basis (Fin (Module.finrank K L)) (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  letI := B.β.toAlgebra
  (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map B.tensorEquiv.toLinearEquiv

private theorem adeleBasis_apply (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (i : Fin (Module.finrank K L)) :
    (letI := B.β.toAlgebra; adeleBasis K L B i) = algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K L i) := by
  letI := B.β.toAlgebra
  show ((Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map
    B.tensorEquiv.toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  exact B.tensorEquiv_one_tmul _

open scoped TensorProduct.RightActions in

private def piBasis (v : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  ((Module.finBasis K L).rightBaseChange L).map
    (LinearEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v).toLinearMap
      (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v))

open scoped TensorProduct.RightActions in
private theorem piBasis_apply (v : HeightOneSpectrum (𝓞 K)) (i : Fin (Module.finrank K L)) :
    piBasis K L v i =
      algebraMap L (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (Module.finBasis K L i) := by
  show (((Module.finBasis K L).rightBaseChange L).map _) i = _
  rw [Module.Basis.map_apply, Module.Basis.rightBaseChange_apply, LinearEquiv.ofBijective_apply]
  exact SemialgHom.baseChange_of_algebraMap_tmul_left
    (HeightOneSpectrum.adicCompletion.semialgHomPi K L (𝓞 L) v) _

private theorem projPi_algebraMap (v : HeightOneSpectrum (𝓞 K)) (l : L) :
    projPi K L v (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap L (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) l := by
  funext w
  rw [projPi_apply, Pi.algebraMap_apply]
  exact NumberField.AdeleRing.algebraMap_snd_apply (𝓞 L) L l w.1

private theorem projPi_smul (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K))
    (r : AdeleRing (𝓞 K) K) (s : AdeleRing (𝓞 L) L) :
    projPi K L v (B.β r * s) =
      algebraMap (v.adicCompletion K) (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L)
        ((r.2 : FiniteAdeleRing (𝓞 K) K) v) * projPi K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projPi_apply, Pi.algebraMap_apply, (M4aHerbrand.adeleBaseChange_local_rigidity K L B).1 r w.1]
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

private theorem adelicNorm_algebraMap (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (l : L) :
    B.adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K l) := by
  letI := B.β.toAlgebra
  refine (norm_transport (Module.finBasis K L) (adeleBasis K L B)
    (algebraMap K (AdeleRing (𝓞 K) K)) (algebraMap L (AdeleRing (𝓞 L) L))
    (fun r s => ?_) (fun i => (adeleBasis_apply K L B i).symm) l).symm
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact (B.β_compat r).symm

private theorem idelicNorm_principal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (α : Lˣ) :
    B.idelicNorm (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α) := by
  apply Units.ext
  show B.adelicNorm (algebraMap L (AdeleRing (𝓞 L) L) (α : L)) =
    algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K (α : L))
  exact adelicNorm_algebraMap K L B (α : L)

private theorem y_eq_idelicNorm_x (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (u : (AdeleRing (𝓞 L) L)ˣ) (α : Lˣ) :
    B.idelicNorm u *
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ =
      B.idelicNorm (u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹) := by
  rw [map_mul, map_inv, idelicNorm_principal]

private theorem adelicNorm_fin_at (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    letI := B.β.toAlgebra
    letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    ((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v =
      ∏ w : v.Extension (𝓞 L),
        Algebra.norm (v.adicCompletion K) ((x.2 : FiniteAdeleRing (𝓞 L) L) w.1) := by
  letI := B.β.toAlgebra
  letI hft : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  haveI : ∀ w : v.Extension (𝓞 L), Module.Free (v.adicCompletion K) (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  have h1 : ((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v =
      Algebra.norm (v.adicCompletion K) (projPi K L v x) := by
    exact norm_transport (adeleBasis K L B) (piBasis K L v)
      ((evalAt K v).comp (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) (projPi K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projPi_smul K L B v r s)
      (fun i => by rw [adeleBasis_apply, piBasis_apply, projPi_algebraMap]) x
  rw [h1, norm_pi]
  rfl

private theorem localNorm_congr_descent (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (m : ℕ)
    (y : w.1.adicCompletion L)
    (hy_unit : Valued.v y = 1)
    (hy_cong : Valued.v (y - 1) ≤
      WithZero.exp (-(Ideal.ramificationIdx' v.asIdeal w.1.asIdeal * m : ℤ))) :
    Valued.v (Algebra.norm (v.adicCompletion K) y) = 1 ∧
    Valued.v (Algebra.norm (v.adicCompletion K) y - 1) ≤ WithZero.exp (-(m : ℤ)) :=
  L3.mainLemma m y hy_unit hy_cong

private theorem prod_congr_one {R : Type*} [Field R] [Valued R (WithZero (Multiplicative ℤ))]
    {ι : Type*} [Fintype ι] (f : ι → R) (m : ℤ)
    (hunit : ∀ i, Valued.v (f i) = 1) (hcong : ∀ i, Valued.v (f i - 1) ≤ WithZero.exp (-m)) :
    Valued.v (∏ i, f i) = 1 ∧ Valued.v (∏ i, f i - 1) ≤ WithZero.exp (-m) := by
  classical
  suffices h : ∀ s : Finset ι, Valued.v (∏ j ∈ s, f j) = 1 ∧
      Valued.v (∏ j ∈ s, f j - 1) ≤ WithZero.exp (-m) by
    exact h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    constructor
    · rw [map_mul, hunit i, ih.1, one_mul]
    ·
      have key : f i * ∏ j ∈ s, f j - 1 =
          (f i - 1) * ∏ j ∈ s, f j + (∏ j ∈ s, f j - 1) := by ring
      rw [key]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ih.2)
      rw [map_mul, ih.1, mul_one]
      exact hcong i

section Arch

open NumberField.InfinitePlace M4aHerbrand.ArchSemilocal
open scoped NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

private def projInf (v : InfinitePlace K) : AdeleRing (𝓞 L) L →+* (∀ w : v.Extension L, w.1.Completion) :=
  RingHom.pi fun w => (Pi.evalRingHom (fun w' : InfinitePlace L => w'.Completion) w.1).comp
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

omit [NumberField K] in
private theorem projInf_apply (v : InfinitePlace K) (x : AdeleRing (𝓞 L) L) (w : v.Extension L) :
    projInf K L v x w = (x.1 : InfiniteAdeleRing L) w.1 := rfl

private def piBasisInf (v : InfinitePlace K) :
    Module.Basis (Fin (Module.finrank K L)) v.Completion (∀ w : v.Extension L, w.1.Completion) :=
  (Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv

private theorem piBasisInf_apply (v : InfinitePlace K) (i : Fin (Module.finrank K L)) :
    piBasisInf K L v i = algebraMap L (∀ w : v.Extension L, w.1.Completion) (Module.finBasis K L i) := by
  show ((Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  funext w
  show psi (K := K) (L := L) v ((1 : v.Completion) ⊗ₜ[K] Module.finBasis K L i) w = _
  rw [psi_apply, psiFactor_one_tmul]
  rfl

omit [NumberField K] in
private theorem projInf_algebraMap (v : InfinitePlace K) (l : L) :
    projInf K L v (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) l := by
  funext w
  rw [projInf_apply, Pi.algebraMap_apply]
  exact NumberField.AdeleRing.algebraMap_fst_apply (𝓞 L) L l w.1

private theorem conorm_apply_ext (x : InfiniteAdeleRing K) (v : InfinitePlace K) (w : v.Extension L) :
    (genuineInfinitePlaceData (K := K) (L := L)).conorm x w.1 = algebraMap v.Completion w.1.Completion (x v) := by
  obtain ⟨w, rfl⟩ := w
  haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  show psiFactor (w.comap (algebraMap K L)) w ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [psiFactor_tmul, map_one, mul_one]

private theorem projInf_smul (v : InfinitePlace K) (r : AdeleRing (𝓞 K) K) (s : AdeleRing (𝓞 L) L) :
    projInf K L v ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).β r * s) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) ((r.1 : InfiniteAdeleRing K) v)
        * projInf K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projInf_apply, Pi.algebraMap_apply, M4aHerbrand.GenuineDescent.genuineBaseChange_β,
    M4aHerbrand.Bridge.genuineβ_fst]
  exact conorm_apply_ext K L r.1 v w

open scoped Classical in

private theorem adelicNorm_fst_apply (x : AdeleRing (𝓞 L) L) (v : InfinitePlace K) :
    (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm x).1 : InfiniteAdeleRing K) v =
      ∏ w : v.Extension L, Algebra.norm v.Completion ((x.1 : InfiniteAdeleRing L) w.1) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
  have h1 : (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm x).1 : InfiniteAdeleRing K) v =
      Algebra.norm v.Completion (projInf K L v x) :=
    norm_transport (adeleBasis K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)) (piBasisInf K L v)
      ((Pi.evalRingHom (fun v' : InfinitePlace K => v'.Completion) v).comp
        (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) (projInf K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projInf_smul K L v r s)
      (fun i => by rw [adeleBasis_apply, piBasisInf_apply, projInf_algebraMap]) x
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [h1, norm_pi]
  rfl

omit [NumberField K] [NumberField L] in

private theorem finrank_completion_eq (v : InfinitePlace K) (w : v.Extension L) :
    Module.finrank v.Completion w.1.Completion = 1 ∨
      (Module.finrank v.Completion w.1.Completion = 2 ∧ v.IsReal ∧ ¬ w.1.IsUnramified K) := by
  by_cases h : w.1.IsUnramified K
  · exact Or.inl (Completion.finrank_eq_one_of_isUnramified v h)
  · refine Or.inr ⟨Completion.finrank_eq_two_of_isRamified v h, ?_, h⟩
    have hr := (InfinitePlace.isRamified_iff.mp h).2
    rwa [w.2] at hr

omit [NumberField K] [NumberField L] in

private theorem exists_sq_eq_of_pos (v : InfinitePlace K) (hv : v.IsReal) (t : v.Completion)
    (ht : 0 < Completion.extensionEmbeddingOfIsReal hv t) : ∃ c : v.Completion, c ^ 2 = t := by
  obtain ⟨c, hc⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv
    (Real.sqrt (Completion.extensionEmbeddingOfIsReal hv t))
  refine ⟨c, (Completion.bijective_extensionEmbeddingOfIsReal hv).1 ?_⟩
  rw [map_pow, hc, Real.sq_sqrt ht.le]

open _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace in

private noncomputable def reparam (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L :=
  (letI := B.β.toAlgebra; B.tensorEquiv.symm.toRingEquiv).trans
    (letI := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra;
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).tensorEquiv.toRingEquiv)

private theorem adelicNorm_eq_norm_tensor (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L) :
    B.adelicNorm x = Algebra.norm (AdeleRing (𝓞 K) K)
      ((letI := B.β.toAlgebra; B.tensorEquiv.symm.toRingEquiv) x :
        (AdeleRing (𝓞 K) K) ⊗[K] L) := by
  letI := B.β.toAlgebra
  exact (Algebra.norm_eq_of_algEquiv B.tensorEquiv.symm x).symm

private theorem adelicNorm_eq_genuine (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L) :
    B.adelicNorm x =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm (reparam K L B x) := by
  rw [adelicNorm_eq_norm_tensor K L B x,
    adelicNorm_eq_norm_tensor K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
      (reparam K L B x)]
  congr 1
  show _ = (letI := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra;
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).tensorEquiv.symm.toRingEquiv)
      ((reparam K L B) x)
  unfold reparam
  rw [RingEquiv.trans_apply]
  exact (RingEquiv.symm_apply_apply _ _).symm

section L4Direct

open scoped Classical

private noncomputable def archPlace (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (w : InfinitePlace L) :
    InfinitePlace K :=
  ((M4aHerbrand.adeleBaseChange_local_rigidity K L B).2 w).choose

private noncomputable def archTheta (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (w : InfinitePlace L) :
    ℂ ≃+* ℂ :=
  (((M4aHerbrand.adeleBaseChange_local_rigidity K L B).2 w).choose_spec).choose

private theorem archChar (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (w : InfinitePlace L)
    (a : AdeleRing (𝓞 K) K) :
    Completion.extensionEmbedding w (((B.β a).1 : InfiniteAdeleRing L) w) =
      archTheta K L B w
        (Completion.extensionEmbedding (archPlace K L B w)
          ((a.1 : InfiniteAdeleRing K) (archPlace K L B w))) :=
  (((M4aHerbrand.adeleBaseChange_local_rigidity K L B).2 w).choose_spec).choose_spec a

private theorem archPlace_isReal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (w : InfinitePlace L)
    (hw : w.IsReal) : (archPlace K L B w).IsReal := by
  by_contra habs
  have hvc : (archPlace K L B w).IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 habs
  obtain ⟨c, hc⟩ := Completion.surjective_extensionEmbedding_of_isComplex hvc Complex.I
  have hkey := archChar K L B w ((Pi.single (archPlace K L B w) c, 0) : AdeleRing (𝓞 K) K)
  have ha : ((((Pi.single (archPlace K L B w) c, 0) : AdeleRing (𝓞 K) K).1 :
      InfiniteAdeleRing K) (archPlace K L B w)) = c := by
    show (Pi.single (M := fun v' : InfinitePlace K => v'.Completion)
      (archPlace K L B w) c) (archPlace K L B w) = c
    exact Pi.single_eq_same _ _
  rw [ha, hc] at hkey
  have him : (archTheta K L B w Complex.I).im = 0 := by
    rw [← hkey, ← Completion.extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_im]
  have hsq : (archTheta K L B w Complex.I) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    exact (archTheta K L B w).map_neg_one
  have hzre : archTheta K L B w Complex.I = ((archTheta K L B w Complex.I).re : ℂ) := by
    rw [Complex.ext_iff]
    exact ⟨(Complex.ofReal_re _).symm, by rw [him, Complex.ofReal_im]⟩
  rw [hzre] at hsq
  have hre : ((archTheta K L B w Complex.I).re ^ 2 : ℝ) = -1 := by
    have h2 := congrArg Complex.re hsq
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at h2
    exact h2
  nlinarith [sq_nonneg (archTheta K L B w Complex.I).re]

private theorem archTheta_ofReal_of_isReal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)
    (w : InfinitePlace L) (hw : w.IsReal) (r : ℝ) :
    archTheta K L B w (r : ℂ) = (r : ℂ) := by
  have hvr : (archPlace K L B w).IsReal := archPlace_isReal K L B w hw
  have hθim : ∀ s : ℝ, (archTheta K L B w (s : ℂ)).im = 0 := by
    intro s
    obtain ⟨cs, hcs⟩ := Completion.surjective_extensionEmbeddingOfIsReal hvr s
    have hkeys := archChar K L B w ((Pi.single (archPlace K L B w) cs, 0) : AdeleRing (𝓞 K) K)
    have has : ((((Pi.single (archPlace K L B w) cs, 0) : AdeleRing (𝓞 K) K).1 :
        InfiniteAdeleRing K) (archPlace K L B w)) = cs := by
      show (Pi.single (M := fun v' : InfinitePlace K => v'.Completion)
        (archPlace K L B w) cs) (archPlace K L B w) = cs
      exact Pi.single_eq_same _ _
    rw [has, ← Completion.extensionEmbeddingOfIsReal_apply hvr, hcs] at hkeys
    rw [← hkeys, ← Completion.extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_im]
  let θ' : ℝ →+* ℝ :=
    { toFun := fun s => (archTheta K L B w (s : ℂ)).re
      map_zero' := by simp
      map_one' := by simp
      map_add' := fun s t => by push_cast; rw [map_add, Complex.add_re]
      map_mul' := fun s t => by
        push_cast; rw [map_mul, Complex.mul_re, hθim s, hθim t, mul_zero, sub_zero] }
  have hθeq : archTheta K L B w (r : ℂ) = ((θ' r : ℝ) : ℂ) := by
    rw [Complex.ext_iff]
    exact ⟨(Complex.ofReal_re _).symm, by rw [Complex.ofReal_im, hθim r]⟩
  rw [hθeq, Real.ringHom_apply θ']

private theorem archPlace_eq_comap_of_isReal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)
    (w : InfinitePlace L) (hw : w.IsReal) :
    archPlace K L B w = w.comap (algebraMap K L) := by
  have hvr : (archPlace K L B w).IsReal := archPlace_isReal K L B w hw
  have hvc : (w.comap (algebraMap K L)).IsReal := InfinitePlace.IsReal.comap _ hw
  apply InfinitePlace.embedding_injective (K := K)
  rw [InfinitePlace.comap_embedding_of_isReal (algebraMap K L) hvc]
  ext k
  have hk := archChar K L B w (algebraMap K (AdeleRing (𝓞 K) K) k)
  rw [B.β_compat k, NumberField.AdeleRing.algebraMap_fst_apply (𝓞 L) L (algebraMap K L k) w,
    NumberField.AdeleRing.algebraMap_fst_apply (𝓞 K) K k (archPlace K L B w)] at hk
  have hθ : archTheta K L B w ((archPlace K L B w).embedding k) =
      (archPlace K L B w).embedding k := by
    rw [← InfinitePlace.embedding_of_isReal_apply hvr]
    exact archTheta_ofReal_of_isReal K L B w hw (InfinitePlace.embedding_of_isReal hvr k)
  simp only [show algebraMap L w.Completion (algebraMap K L k) =
        ((algebraMap K L k : WithAbs w.1) : w.Completion) from rfl,
    show algebraMap K (archPlace K L B w).Completion k =
        ((k : WithAbs (archPlace K L B w).1) : (archPlace K L B w).Completion) from rfl,
    Completion.extensionEmbedding_coe] at hk
  simp only [WithAbs.equiv_apply, hθ, RingHom.comp_apply] at hk ⊢
  exact hk.symm

private theorem beta_fst_eq_genuine_of_isReal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)
    (a : AdeleRing (𝓞 K) K) (w : InfinitePlace L) (hw : w.IsReal) :
    ((B.β a).1 : InfiniteAdeleRing L) w =
      (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).β a).1 : InfiniteAdeleRing L) w := by
  apply (Completion.extensionEmbedding w).injective
  rw [archChar K L B w a, archChar K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L) w a,
    archPlace_eq_comap_of_isReal K L B w hw,
    archPlace_eq_comap_of_isReal K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L) w hw]
  have hvc : (w.comap (algebraMap K L)).IsReal := InfinitePlace.IsReal.comap _ hw
  rw [← Completion.extensionEmbeddingOfIsReal_apply hvc,
    archTheta_ofReal_of_isReal K L B w hw,
    archTheta_ofReal_of_isReal K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L) w hw]

private theorem reparam_fst_of_isReal (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)
    (x : AdeleRing (𝓞 L) L) (w : InfinitePlace L) (hw : w.IsReal) :
    ((reparam K L B x).1 : InfiniteAdeleRing L) w = (x.1 : InfiniteAdeleRing L) w := by
  let Bg := M4aHerbrand.GenuineDescent.genuineBaseChange K L
  have hte : ∀ y : (AdeleRing (𝓞 K) K) ⊗[K] L,
      ((letI := B.β.toAlgebra; B.tensorEquiv y).1 : InfiniteAdeleRing L) w =
      ((letI := Bg.β.toAlgebra; Bg.tensorEquiv y).1 : InfiniteAdeleRing L) w := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
    | tmul a l =>
      have hBte : ∀ B' : AdeleBaseChange (𝓞 K) K (𝓞 L) L,
          (letI := B'.β.toAlgebra; B'.tensorEquiv (a ⊗ₜ[K] l)) =
            B'.β a * algebraMap L (AdeleRing (𝓞 L) L) l := by
        intro B'; letI := B'.β.toAlgebra
        have hsm : (a ⊗ₜ[K] l : (AdeleRing (𝓞 K) K) ⊗[K] L) =
            a • ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hsm, map_smul, B'.tensorEquiv_one_tmul l, Algebra.smul_def]
        rfl
      rw [hBte B, hBte Bg]
      show ((B.β a).1 : InfiniteAdeleRing L) w *
            ((algebraMap L (AdeleRing (𝓞 L) L) l).1 : InfiniteAdeleRing L) w =
        ((Bg.β a).1 : InfiniteAdeleRing L) w *
            ((algebraMap L (AdeleRing (𝓞 L) L) l).1 : InfiniteAdeleRing L) w
      rw [beta_fst_eq_genuine_of_isReal K L B a w hw]
    | add y₁ y₂ ih₁ ih₂ =>
      simp only [map_add]
      show ((letI := B.β.toAlgebra; B.tensorEquiv y₁).1 : InfiniteAdeleRing L) w +
            ((letI := B.β.toAlgebra; B.tensorEquiv y₂).1 : InfiniteAdeleRing L) w =
        ((letI := Bg.β.toAlgebra; Bg.tensorEquiv y₁).1 : InfiniteAdeleRing L) w +
            ((letI := Bg.β.toAlgebra; Bg.tensorEquiv y₂).1 : InfiniteAdeleRing L) w
      rw [ih₁, ih₂]
  show ((letI := Bg.β.toAlgebra; Bg.tensorEquiv
      (letI := B.β.toAlgebra; B.tensorEquiv.symm x)).1 : InfiniteAdeleRing L) w = _
  rw [← hte]
  letI := B.β.toAlgebra
  rw [AlgEquiv.apply_symm_apply]

end L4Direct
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3"

open _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace M4aHerbrand.ArchSemilocal in
open scoped Classical in

private theorem L4_realPos_genuine (x : (AdeleRing (𝓞 L) L)ˣ)
    (hpos : ∀ (w : InfinitePlace L) (hw : w.IsReal),
      0 < Completion.extensionEmbeddingOfIsReal hw
        ((((x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w))
    (v : InfinitePlace K) (hv : v.IsReal) :
    0 < Completion.extensionEmbeddingOfIsReal hv
      (((((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm x :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v) := by
  rw [show (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm x :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm
        (x : AdeleRing (𝓞 L) L) from rfl]
  rw [adelicNorm_fst_apply (K := K) (L := L), map_prod]
  refine Finset.prod_pos ?_
  intro w _
  have hzne : ((x : AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w.1 ≠ 0 := by
    have hu := x.isUnit.map ((Pi.evalRingHom (fun w' : InfinitePlace L => w'.Completion) w.1).comp
      (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)))
    exact hu.ne_zero
  set z : w.1.Completion := ((x : AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w.1 with hz_def
  rcases finrank_completion_eq (K := K) (L := L) v w with h1 | ⟨h2, _, hram⟩
  ·
    have hun : w.1.IsUnramified K := by
      by_contra habs
      have := Completion.finrank_eq_two_of_isRamified (K := K) (L := L) v (w := w.1) habs
      omega
    have hwr : w.1.IsReal := by
      refine (InfinitePlace.isUnramified_iff.mp hun).resolve_right ?_
      rw [w.2]
      exact InfinitePlace.not_isComplex_iff_isReal.mpr hv
    have hlies := LiesOver.extensionEmbedding_liesOver_of_isReal w.1 (v := v) hv
    rw [Algebra.norm_eq_of_equiv_equiv (Completion.ringEquivRealOfIsReal hv)
        (Completion.ringEquivRealOfIsReal hwr)
        (RingHom.ext fun _ => Complex.ofReal_inj.1 <| by simp) z]
    have hcancel : ∀ r : ℝ,
        Completion.extensionEmbeddingOfIsReal hv
          ((Completion.ringEquivRealOfIsReal hv).symm r) = r := by
      intro r
      rw [← Completion.ringEquivRealOfIsReal_apply hv, RingEquiv.apply_symm_apply]
    rw [hcancel, show (Algebra.norm ℝ) ((Completion.ringEquivRealOfIsReal hwr) z) =
        (Completion.ringEquivRealOfIsReal hwr) z from by rw [Algebra.norm_self]; rfl,
      Completion.ringEquivRealOfIsReal_apply]
    exact hpos w.1 hwr
  ·
    have hwc : w.1.IsComplex := by
      have hrat := (InfinitePlace.isRamified_iff (K := L) (k := K)).mp hram
      exact hrat.1
    have hlies := LiesOver.extensionEmbedding_liesOver_of_isReal w.1 (v := v) hv
    rw [Algebra.norm_eq_of_equiv_equiv (Completion.ringEquivRealOfIsReal hv)
        (Completion.ringEquivComplexOfIsComplex hwc) (by ext; simp) z]
    have hcancel : ∀ r : ℝ,
        Completion.extensionEmbeddingOfIsReal hv
          ((Completion.ringEquivRealOfIsReal hv).symm r) = r := by
      intro r
      rw [← Completion.ringEquivRealOfIsReal_apply hv, RingEquiv.apply_symm_apply]
    rw [hcancel, Algebra.norm_complex_apply]
    refine Complex.normSq_pos.mpr ?_
    simp only [ne_eq, EmbeddingLike.map_eq_zero_iff]
    exact hzne

end Arch
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3"

open NumberField.InfinitePlace in

private noncomputable def reparamUnit (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    (AdeleRing (𝓞 L) L)ˣ ≃* (AdeleRing (𝓞 L) L)ˣ :=
  Units.mapEquiv (reparam K L B).toMulEquiv

private theorem adelicNorm_realPos (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : (AdeleRing (𝓞 L) L)ˣ)
    (hpos : ∀ (w : InfinitePlace L) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((((x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w))
    (v : InfinitePlace K) (hv : v.IsReal) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((((B.idelicNorm x : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v) := by
  have h1 : ((B.idelicNorm x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (reparamUnit K L B x) :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := by
    show B.adelicNorm (x : AdeleRing (𝓞 L) L) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm
        ((reparamUnit K L B x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    rw [show ((reparamUnit K L B x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
        reparam K L B (x : AdeleRing (𝓞 L) L) from rfl]
    exact adelicNorm_eq_genuine K L B (x : AdeleRing (𝓞 L) L)
  rw [h1]
  refine L4_realPos_genuine K L (reparamUnit K L B x) (fun w hw => ?_) v hv
  rw [show (((reparamUnit K L B x : (AdeleRing (𝓞 L) L)ˣ) :
      AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w =
    ((x : AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w from
      reparam_fst_of_isReal K L B (x : AdeleRing (𝓞 L) L) w hw]
  exact hpos w hw

private theorem a1_yval_fin (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (u : (AdeleRing (𝓞 L) L)ˣ) (α : Lˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    (((B.idelicNorm u *
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v =
      ∏ w : v.Extension (𝓞 L),
        Algebra.norm (v.adicCompletion K)
          ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
            AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w.1) := by
  letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  rw [y_eq_idelicNorm_x K L B u α]
  exact adelicNorm_fin_at K L B _ v

private theorem ext_dvd_map (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv𝔣 : v.asIdeal ∣ 𝔣)
    (w : v.Extension (𝓞 L)) :
    w.1.asIdeal ∣ 𝔣.map (algebraMap (𝓞 K) (𝓞 L)) := by
  refine Ideal.dvd_iff_le.mpr (le_trans (Ideal.map_mono (Ideal.le_of_dvd hv𝔣)) ?_)
  have hcomap : v.asIdeal = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.1.asIdeal := by
    rw [← Ideal.under_def, ← HeightOneSpectrum.under_asIdeal, w.2]
  rw [hcomap]
  exact Ideal.map_comap_le

private theorem ext_count_eq_mul (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) :
    (Associates.mk w.1.asIdeal).count
        (Associates.mk (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).factors =
      Ideal.ramificationIdx' v.asIdeal w.1.asIdeal *
        (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors := by
  have hct := HeightOneSpectrum.mk_count_factors_map (A := 𝓞 K) (B := 𝓞 L)
    (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1 𝔣
  rw [w.2] at hct
  exact hct

private theorem a1_impl
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 L) L)ˣ) (α : Lˣ)
    (hcong : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ 𝔣.map (algebraMap (𝓞 K) (𝓞 L)) →
      Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w) = 1 ∧
        Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
            AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w - 1) ≤
          WithZero.exp (-((Associates.mk w.asIdeal).count
            (Associates.mk (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).factors : ℤ)))
    (hpos : ∀ (w : InfinitePlace L) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w)) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
        Valued.v ((((B.idelicNorm u *
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
              (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
          WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v) := by
  refine ⟨fun v hv𝔣 => ?_, fun v hv => ?_⟩
  ·
    letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    rw [a1_yval_fin K L B u α v]
    refine prod_congr_one _ ((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)
      (fun w => ?_) (fun w => ?_)
    ·
      rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg K L v w,
        (hcong w.1 (ext_dvd_map K L 𝔣 v hv𝔣 w)).1, one_pow]
    ·
      have hc := hcong w.1 (ext_dvd_map K L 𝔣 v hv𝔣 w)
      refine (localNorm_congr_descent K L v w
        ((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors)
        _ hc.1 ?_).2
      have hcast : (Ideal.ramificationIdx' v.asIdeal w.1.asIdeal *
            (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ) =
          ((Associates.mk w.1.asIdeal).count
            (Associates.mk (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).factors : ℤ) := by
        exact_mod_cast (ext_count_eq_mul K L 𝔣 v w).symm
      rw [hcast]
      exact hc.2
  ·
    rw [y_eq_idelicNorm_x K L B u α]
    exact adelicNorm_realPos K L B _ hpos v hv

end A
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3"

end AdelicNormLevelDescent
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3 P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent"

end
p2m_reactivate "P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent.L3 P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos.AdelicNormLevelDescent"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 L) L)ˣ) (α : Lˣ)
    (hcong : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ 𝔣.map (algebraMap (𝓞 K) (𝓞 L)) →
      Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w) = 1 ∧
        Valued.v ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
            AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) w - 1) ≤
          WithZero.exp (-((Associates.mk w.asIdeal).count
            (Associates.mk (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).factors : ℤ)))
    (hpos : ∀ (w : InfinitePlace L) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((((u * (Units.map (algebraMap L (AdeleRing (𝓞 L) L)) α)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).1 : InfiniteAdeleRing L) w)) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
        Valued.v ((((B.idelicNorm u *
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
              (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
          WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        ((((B.idelicNorm u *
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.map (Algebra.norm K) α))⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v) :=
  AdelicNormLevelDescent.a1_impl K L B 𝔣 u α hcong hpos

end S_M4aHerbrand_idelicNorm_levelCongr_and_realPos
end P2MW
export P2MW.S_M4aHerbrand_idelicNorm_levelCongr_and_realPos (solution)
